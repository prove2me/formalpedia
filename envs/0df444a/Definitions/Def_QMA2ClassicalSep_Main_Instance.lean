-- Prove2me | Definitions.Def_QMA2ClassicalSep_Main_Instance
-- name    : QMA2ClassicalSep_Main_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:18.100402+00:00
-- url     : https://prove2.me/theorems/efedfdac-00fe-4055-9b82-82894a1899c0
-- title:
--   §4 — signed cycle covers, the Hamiltonian $H$, $\lambda_{\mathrm{sep}}$ and oracle (2)
-- statement:
--   Let $\mathcal X_A,\mathcal X_B$ be two copies of $\{0,1\}^\ell$ (a set of size $2^\ell$) and $V=\mathcal X_A\times\mathcal X_B$; a vertex $v=(x_A,x_B)$ is the basis state $|x_A\rangle_A|x_B\rangle_B$. Let $N=2^k$; indices $p\in[N]$ are written as $k$-bit strings. An **instance** of Problem 4.1 consists of permutations $\pi_p$ of $V$ and sign bits $b_p(v)$, the edge $v\to\pi_p(v)$ carrying the sign $\sigma_p(v)=(-1)^{b_p(v)}$ (self-loops and parallel edges are allowed).
--
--   From these,
--   $$
--   U_p|v\rangle=\sigma_p(v)|\pi_p(v)\rangle,\quad \Gamma_p=\tfrac12(U_p+U_p^\dagger),\quad H_p=\tfrac12(\mathbb I-\Gamma_p),\quad H=\frac1N\sum_{p\in[N]}H_p,\quad \Gamma=\frac1N\sum_p\Gamma_p .
--   $$
--   The **minimum separable energy** is $\lambda_{\mathrm{sep}}(H)=\min_{\|\alpha\|=\|\beta\|=1}\langle\alpha|\langle\beta|H|\alpha\rangle|\beta\rangle$ over unit $\alpha\in\mathbb C^{\mathcal X_A}$, $\beta\in\mathbb C^{\mathcal X_B}$. The YES case is $\lambda_{\mathrm{sep}}(H)\le 3/16$, the NO case $\lambda_{\mathrm{sep}}(H)\ge1/4$.
--
--   **Oracle (2).** $O(p,0,v)=(\pi_p(v),b_p(v))$ and $O(p,1,v)=(\pi_p^{-1}(v),b_p(\pi_p^{-1}(v)))$, queried through $U_O|p,z,v,w\rangle=|p,z,v,w\oplus O(p,z,v)\rangle$ on the query register (address $(p,z,v)$, answer $w$ of $2\ell+1$ bits).
--
--   These objects are the black-box problem of the separation: the Hamiltonian is never given explicitly, only through oracle (2).
--
--   **Formalization Note** $\lambda_{\mathrm{sep}}$ is written as an infimum of the real set of product-state energies; the set is nonempty and compact, so it is the minimum. The direction bit $z$ is a `Bool` (`false` = forward).
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, Section 4, pp. 15–17: vertex space, signed cycle covers, Equation (1), Problem 4.1, Equation (2) and the query unitary U_O

import Mathlib

set_option autoImplicit false

/-!
# Section 4: signed cycle covers, the Hamiltonian, the separable energy and oracle (2)

Grewal, Mutreja, Tomer, *A classical oracle separation between QMA and QMA(2)*, STOC 2027
submission #618, Section 4, pp. 15–17.
-/

namespace QMA2ClassicalSep.Main

open Matrix

/-- An `ℓ`-bit string: an element of one side `𝒳_A` or `𝒳_B` (a set of size `2^ℓ`). -/
abbrev Coord (ℓ : ℕ) := Fin ℓ → Bool

/-- A vertex `v = (x_A, x_B) ∈ V = 𝒳_A × 𝒳_B`. -/
abbrev Vtx (ℓ : ℕ) := Coord ℓ × Coord ℓ

/-- A permutation index `p ∈ [N]`, `N = 2^k`, written as a `k`-bit string. -/
abbrev PIdx (k : ℕ) := Fin k → Bool

/-- An instance of Problem 4.1: for each `p ∈ [N]` a permutation `π_p` of `V` and a sign bit
`b_p(v)`, the sign of the directed edge `v → π_p(v)` being `σ_p(v) = (−1)^{b_p(v)}`. Self-loops
and parallel edges are allowed. -/
structure SignedInstance (k ℓ : ℕ) where
  perm : PIdx k → Equiv.Perm (Vtx ℓ)
  bit : PIdx k → Vtx ℓ → Bool

namespace SignedInstance

variable {k ℓ : ℕ} (inst : SignedInstance k ℓ)

/-- `σ_p(v) = (−1)^{b_p(v)} ∈ {±1}`. -/
def sgn (p : PIdx k) (v : Vtx ℓ) : ℂ := if inst.bit p v then -1 else 1

/-- `U_p |v⟩ = σ_p(v) |π_p(v)⟩`. -/
noncomputable def U (p : PIdx k) : Matrix (Vtx ℓ) (Vtx ℓ) ℂ :=
  fun u v => if u = inst.perm p v then inst.sgn p v else 0

/-- `Γ_p = (U_p + U_p†)/2`. -/
noncomputable def Gam (p : PIdx k) : Matrix (Vtx ℓ) (Vtx ℓ) ℂ :=
  (1 / 2 : ℂ) • (inst.U p + (inst.U p)ᴴ)

/-- `H_p = (𝕀 − Γ_p)/2`. -/
noncomputable def Hp (p : PIdx k) : Matrix (Vtx ℓ) (Vtx ℓ) ℂ :=
  (1 / 2 : ℂ) • (1 - inst.Gam p)

/-- `Γ = (1/N) Σ_p Γ_p`. -/
noncomputable def GamAvg : Matrix (Vtx ℓ) (Vtx ℓ) ℂ :=
  (1 / (2 ^ k : ℂ)) • ∑ p, inst.Gam p

/-- The Hamiltonian of Equation (1): `H = (1/N) Σ_{p ∈ [N]} H_p`. -/
noncomputable def Ham : Matrix (Vtx ℓ) (Vtx ℓ) ℂ :=
  (1 / (2 ^ k : ℂ)) • ∑ p, inst.Hp p

end SignedInstance

/-- A vector of `ℂ^ι` is a unit vector: `Σ_i |ψ_i|² = 1`. -/
def IsUnit' {ι : Type*} [Fintype ι] (ψ : ι → ℂ) : Prop := ∑ i, Complex.normSq (ψ i) = 1

/-- The product vector `|α⟩_A ⊗ |β⟩_B`, with amplitude `a_{x_A} b_{x_B}` at `(x_A, x_B)`. -/
def prodVec {ℓ : ℕ} (α β : Coord ℓ → ℂ) : Vtx ℓ → ℂ := fun v => α v.1 * β v.2

/-- The expectation `⟨ψ| M |ψ⟩` (real part). -/
noncomputable def expect {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (ψ : ι → ℂ) : ℝ :=
  (star ψ ⬝ᵥ M.mulVec ψ).re

/-- The minimum separable energy `λ_sep(H) = min_{‖α‖ = ‖β‖ = 1} ⟨α|⟨β| H |α⟩|β⟩`, over unit
vectors `α ∈ ℂ^{𝒳_A}`, `β ∈ ℂ^{𝒳_B}`. (The set is nonempty, bounded and compact, so the
infimum is a minimum.) -/
noncomputable def lamSep {ℓ : ℕ} (H : Matrix (Vtx ℓ) (Vtx ℓ) ℂ) : ℝ :=
  sInf {e | ∃ α β : Coord ℓ → ℂ, IsUnit' α ∧ IsUnit' β ∧ e = expect H (prodVec α β)}

/-- YES case of Problem 4.1: `λ_sep(H) ≤ 3/16`. -/
def IsYes {k ℓ : ℕ} (inst : SignedInstance k ℓ) : Prop := lamSep inst.Ham ≤ 3 / 16

/-- NO case of Problem 4.1: `λ_sep(H) ≥ 1/4`. -/
def IsNo {k ℓ : ℕ} (inst : SignedInstance k ℓ) : Prop := 1 / 4 ≤ lamSep inst.Ham

/-- An address `a = (p, z, v)`: permutation index, direction (`false` = forward `z = 0`,
`true` = inverse `z = 1`), and vertex. -/
abbrev Addr (k ℓ : ℕ) := PIdx k × Bool × Vtx ℓ

/-- An answer `(w, t)`: a vertex register and a sign bit (`2ℓ + 1` bits). -/
abbrev Ans (ℓ : ℕ) := Vtx ℓ × Bool

/-- The query register `|p, z, v, w⟩` (address and answer). -/
abbrev QReg (k ℓ : ℕ) := Addr k ℓ × Ans ℓ

instance (ℓ : ℕ) : DecidableEq (Ans ℓ) := instDecidableEqProd
instance (k ℓ : ℕ) : DecidableEq (QReg k ℓ) := instDecidableEqProd
instance (k ℓ : ℕ) : Fintype (QReg k ℓ) := instFintypeProd _ _

/-- Oracle (2): `O(p, 0, v) = (π_p(v), b_p(v))` and
`O(p, 1, v) = (π_p^{-1}(v), b_p(π_p^{-1}(v)))`. -/
def SignedInstance.oracle {k ℓ : ℕ} (inst : SignedInstance k ℓ) (a : Addr k ℓ) : Ans ℓ :=
  match a with
  | (p, false, v) => (inst.perm p v, inst.bit p v)
  | (p, true, v) => ((inst.perm p).symm v, inst.bit p ((inst.perm p).symm v))

/-- Bitwise XOR of two answers. -/
def ansXor {ℓ : ℕ} (w u : Ans ℓ) : Ans ℓ :=
  ((fun i => xor (w.1.1 i) (u.1.1 i), fun i => xor (w.1.2 i) (u.1.2 i)), xor w.2 u.2)

/-- The reversible query `U_O |p, z, v, w⟩ = |p, z, v, w ⊕ O(p, z, v)⟩` on a basis state. -/
def SignedInstance.queryMap {k ℓ : ℕ} (inst : SignedInstance k ℓ) (r : QReg k ℓ) : QReg k ℓ :=
  (r.1, ansXor r.2 (inst.oracle r.1))

/-- The unitary `U_O` as a permutation matrix on the query register. -/
noncomputable def SignedInstance.UO {k ℓ : ℕ} (inst : SignedInstance k ℓ) :
    Matrix (QReg k ℓ) (QReg k ℓ) ℂ :=
  fun r' r => if r' = inst.queryMap r then 1 else 0

/-- The all-zero basis state of the query register. -/
def qzero (k ℓ : ℕ) : QReg k ℓ :=
  ((fun _ => false, false, (fun _ => false, fun _ => false)),
    ((fun _ => false, fun _ => false), false))

end QMA2ClassicalSep.Main


