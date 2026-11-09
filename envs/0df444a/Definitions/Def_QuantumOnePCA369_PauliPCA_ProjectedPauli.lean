-- Prove2me | Definitions.Def_QuantumOnePCA369_PauliPCA_ProjectedPauli
-- name    : QuantumOnePCA369_PauliPCA_ProjectedPauli
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:54.320554+00:00
-- url     : https://prove2.me/theorems/00fb2f26-548d-4c31-9cfd-657b18ebde60
-- title:
--   Algorithm 2: projected Pauli pre-computation by fast Walsh–Hadamard transforms
-- statement:
--   Algorithm 2 of the paper as a costed program.
--
--   **Fourier transform (p. 5).** For $f:\mathbb F_2^m\to\mathbb C^\kappa$, $\mathcal Ff(x)=\hat f(x)=\mathbb E_{y\sim\mathbb F_2^m}f(y)(-1)^{x\cdot y}$ and $\mathcal F^{-1}g(x)=\sum_yg(y)(-1)^{x\cdot y}$. Both are computed by the fast Walsh–Hadamard butterfly, recursing on the first bit,
--   $$\text{out}(by)=c\,\big(g_0(y)+(-1)^bg_1(y)\big),$$
--   with $c=1/2$ for $\mathcal F$ and $c=1$ for $\mathcal F^{-1}$, where $g_a$ is the transform of $y\mapsto f(ay)$; it costs $O(m2^m\kappa)$.
--
--   **Algorithm 2.** Inputs: prefix length $\ell$, suffix length $m$ ($n=\ell+m$), width $k_0$, the number $R$ of pairs, pairs $(A_r,c_r)\in\mathrm{Sym}_m(\mathbb F_2)\times\mathbb F_2^m$, and $2^m\times k_0$ complex matrices $\tilde U_s$, $s\in\{0,1\}^\ell$. For each round $r$ the phases $q(x)=x\cdot A_rx$ (whole matrix lifted, mod 4), $x\cdot c_r$ (mod 2), the label $z(x)=A_rx+c_r$ (over $\mathbb F_2$) and $e(x)=x\cdot(A_rx+c_r)-x\cdot A_rx$ (mod 4) are computed once. Then for every $s$:
--   1. $u_s^{(r)}(x)=i^{x\cdot A_rx}\tilde U_s^\dagger|x\rangle$ and $v_s^{(r)}(x)=i^{x\cdot A_rx}(-1)^{x\cdot c_r}\tilde U_s^\dagger|x\rangle$;
--   2. $\hat u_s^{(r)},\hat v_s^{(r)}$ by the butterfly;
--   3. $$\pi_s^{(r)}(x)=i^{x\cdot(A_rx+c_r)-x\cdot A_rx}\cdot2^{m}\,\mathcal F^{-1}\big(\hat u_s^{(r)}\hat v_s^{(r)\dagger}\big)(x),\qquad x\in\mathbb F_2^m,$$
--   with the inverse transform applied entrywise to the $k_0\times k_0$-valued map by the butterfly.
--
--   The output is the family of $k_0\times k_0$ matrices $\pi_s^{(r)}(x)$.
--
--   **Formalization Note** The paper's inputs $n,\ell,k,R$ become $\ell,m,k_0,R$ with $n=\ell+m$; $k$ only bounds the width $k_0\le2k$ and is imposed where a theorem needs it. The transform is the butterfly recursion: a direct sum over $y$ would cost $4^m$.
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 5 (Fourier transform, outer-product convolution), p. 8, Algorithm 2 (Projected Pauli Pre-computation)

import Mathlib
import Definitions.Def_MITMSynthesis_Timed
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_Cost

namespace QuantumOnePCA369.PauliPCA

open MITMSynthesis

/-! Algorithm 2 (projected Pauli pre-computation), p. 8, as a costed program. -/

/-- The fast Walsh–Hadamard butterfly on vector-valued maps `f : 𝔽₂^m → ℂ^κ`, by recursion on the
first bit: `out(b y) = c · (g₀(y) + (-1)^b g₁(y))`, where `g_a` is the transform of `y ↦ f(a y)`.
With `c = 1/2` it computes the normalized transform `F f(x) = 𝔼_{y ∼ 𝔽₂^m} f(y)(-1)^{x·y}` (p. 5);
with `c = 1` it computes `F⁻¹ g(x) = ∑_y g(y)(-1)^{x·y}`. Cost `O(m 2^m |κ|)`. -/
noncomputable def fwhtC {κ : Type} [Fintype κ] (c : ℂ) :
    (m : ℕ) → (Bits m → κ → ℂ) → Timed (Bits m → κ → ℂ)
  | 0, f => pure f
  | m + 1, f => do
    let g0 ← fwhtC c m (fun y => f (Fin.cons (α := fun _ => ZMod 2) 0 y))
    let g1 ← fwhtC c m (fun y => f (Fin.cons (α := fun _ => ZMod 2) 1 y))
    tab fun x : Bits (m + 1) => tab fun j : κ =>
      op (c * (g0 (Fin.tail x) j + sgn (x 0) * g1 (Fin.tail x) j))

/-- One round `r` of Algorithm 2 for a symmetric `A = A_r ∈ Sym_m(𝔽₂)` and `c = c_r ∈ 𝔽₂^m`, for
all prefixes `s ∈ 𝔽₂^ℓ` at once, where `Ũ_s` (`U s`) is a `2^m × k₀` matrix. The phases
`q(x) = x·Ax` (whole matrix lifted to `ℤ`, mod 4), `x·c` (mod 2), the Pauli label `z = Ax + c`
(over `𝔽₂`) and `e(x) = x·(Ax+c) − x·Ax` (mod 4) are computed once per round. Then, for each `s`:
line 1 `u_s(x) = i^{x·Ax} Ũ_s†|x⟩`, `v_s(x) = i^{x·Ax}(-1)^{x·c} Ũ_s†|x⟩`; line 2 `û_s, v̂_s` by the
butterfly; line 3 `π_s(x) = i^{e(x)} · 2^m · F⁻¹(û_s v̂_s†)(x)` by the butterfly on `k₀ × k₀`-valued
maps. -/
noncomputable def alg2Round (ℓ m k₀ : ℕ) (A : Matrix (Fin m) (Fin m) (ZMod 2)) (c : Bits m)
    (U : Bits ℓ → Matrix (Bits m) (Fin k₀) ℂ) :
    Timed (Bits ℓ → Bits m → Matrix (Fin k₀) (Fin k₀) ℂ) := do
  let q ← tab fun x : Bits m => sumC fun ij : Fin m × Fin m =>
    op (((x ij.1).val * (A ij.1 ij.2).val * (x ij.2).val : ℕ) : ZMod 4)
  let xc ← tab fun x : Bits m => sumC fun j : Fin m => op (x j * c j)
  let z ← tab fun x : Bits m => tab fun i : Fin m => do
    let t ← sumC fun j : Fin m => op (A i j * x j)
    op (t + c i)
  let e ← tab fun x : Bits m => do
    let t ← sumC fun j : Fin m => op ((((x j).val * (z x j).val : ℕ)) : ZMod 4)
    op (t - q x)
  tab fun s : Bits ℓ => do
    let u ← tab fun x : Bits m => tab fun a : Fin k₀ => op (iPow (q x) * star (U s x a))
    let v ← tab fun x : Bits m => tab fun a : Fin k₀ =>
      op (iPow (q x) * sgn (xc x) * star (U s x a))
    let uh ← fwhtC (1 / 2) m u
    let vh ← fwhtC (1 / 2) m v
    let W ← tab fun x : Bits m => tab fun ab : Fin k₀ × Fin k₀ =>
      op (uh x ab.1 * star (vh x ab.2))
    let G ← fwhtC 1 m W
    tab fun x : Bits m => tab fun a : Fin k₀ => tab fun b : Fin k₀ =>
      op (iPow (e x) * (2 : ℂ) ^ m * G x (a, b))

/-- **Algorithm 2 (projected Pauli pre-computation).** Inputs: lengths `ℓ` (prefix) and `m`
(suffix; `n = ℓ + m`), width `k₀`, number of pairs `R`, symmetric matrices `A_r ∈ Sym_m(𝔽₂)`,
vectors `c_r ∈ 𝔽₂^m`, and the `2^m × k₀` matrices `Ũ_s`, `s ∈ 𝔽₂^ℓ`. Output: the `k₀ × k₀`
matrices `π_s^{(r)}(x)` for all `r, s, x`, computed round by round with `alg2Round`. -/
noncomputable def alg2 (ℓ m k₀ R : ℕ) (A : Fin R → SymF2 m) (c : Fin R → Bits m)
    (U : Bits ℓ → Matrix (Bits m) (Fin k₀) ℂ) :
    Timed (Fin R → Bits ℓ → Bits m → Matrix (Fin k₀) (Fin k₀) ℂ) :=
  tab fun r => alg2Round ℓ m k₀ (A r).1 (c r) U

end QuantumOnePCA369.PauliPCA


