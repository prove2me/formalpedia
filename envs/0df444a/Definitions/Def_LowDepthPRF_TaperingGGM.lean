-- Prove2me | Definitions.Def_LowDepthPRF_TaperingGGM
-- name    : LowDepthPRF_TaperingGGM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:29.11498+00:00
-- url     : https://prove2.me/theorems/612d092c-62a6-4a64-90b3-ed12d479351e
-- title:
--   Construction 4.3: the tapering GGM tree (TGGM) and the PRF $\mathscr F'=\mathscr F^{\oplus m}$
-- statement:
--   Fix $\lambda$ and set $m=\lambda$, $\ell=\lceil\log\log\log\lambda\rceil$ and $\Delta=2^{\lceil\log\lambda\rceil}$, with $\lambda^{(1)}=\lambda$ and $\lambda^{(i+1)}=\lceil\sqrt{\lambda^{(i)}}\rceil$. The building blocks are:
--
--   1. a family $G_n:\{0,1\}^{p(n)}\to\{0,1\}^{\lceil\sqrt n\rceil}$ with key $\{0,1\}^n$;
--   2. a hash $H_\lambda:\{0,1\}^\lambda\to[\Delta]^\ell$ with key $\{0,1\}^{kh(\lambda)}$.
--
--   A key of one tree is $k_F=(k_G,k_{XG},k_H)$. Here $k_G\in\{0,1\}^\lambda$ is the root state, $k_{XG}=\{(r^{(i)}_1,\dots,r^{(i)}_\Delta)\}_{i\in[\ell]}$ is the input pool with $r^{(i)}_j\in\{0,1\}^{p(\lambda^{(i)})}$, and $k_H$ is a hash key. On input $x\in\{0,1\}^\lambda$, the tree computes $\tilde x=H_{k_H}(x)$, sets $y^{(1)}=k_G$, and runs **TGGM** (Figure 2):
--
--   $$y^{(i+1)}=G_{\lambda^{(i)}}\bigl(y^{(i)},\,r^{(i)}_{\tilde x_i}\bigr)\in\{0,1\}^{\lambda^{(i+1)}},\qquad i=1,\dots,\ell.$$
--
--   The state $y^{(i)}$ is the key of $G$, and the pool element is its input. The output is $y^{(\ell+1)}$. The PRF $\mathscr F'_\lambda=\mathscr F_\lambda^{\oplus m}$ has $m$ independent tree keys and outputs their XOR. As an ensemble, it has input length $\lambda$, output length $\lambda^{(\ell+1)}$ and a bit-string key of length $m(\lambda+\sum_{i\le\ell}\Delta\,p(\lambda^{(i)})+kh(\lambda))$.
--
--   This is the paper's generic weak-to-strong transformation.
--
--   **Formalization Note**
--   1. $\ell$ uses real base-2 logarithms with a ceiling ($\ell=0$ for $\lambda\le4$), and $\lceil\log\lambda\rceil$ is `Nat.clog 2 λ`.
--   2. The index shifts: `tl λ i` $=\lambda^{(i+1)}$, so paper level $i$ is level $i-1$ here.
--   3. $[\Delta]^\ell$ is $\ell$ blocks of $\log\Delta$ bits, each block read as a binary number, as in the proof of Lemma 4.5.
--   4. The construction is given by the same formulas at every $\lambda$. Statements that need $\lambda$ large say so (the condition $c_q=\lceil2\log_\Delta q\rceil<\ell$).
--   5. The bit-string key is decoded by a fixed bijection of bit positions, which costs no gates and maps uniform strings to uniform keys.
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Construction 4.3, pp.16–18 (pdf 18–20); Figure 2, p.16 (pdf 18); Theorem 4.6 for c_q, p.18 (pdf 20)

import Mathlib
import Definitions.Def_LowDepthPRF_Ensemble

namespace LowDepthPRF

/-!
# Construction 4.3: the tapering GGM tree and the PRF `ℱ′ = ℱ^{⊕m}`

Ding, Jain, Komargodski, *Pseudorandom Functions in NC¹ from LWE/LPN/CDH*, arXiv:2608.25213
(sha256 89a55849…), Construction 4.3, pp.16–18, and Figure 2 (TGGM), p.16.

**Formalization Note.**
* Parameters: `m = λ` trees; `ℓ = ⌈log log log λ⌉` levels (real base-2 logarithms, `Nat.ceil`;
  `ℓ = 0` for `λ ≤ 4`); `Δ = 2^{⌈log λ⌉}` children per node, with `⌈log λ⌉ = Nat.clog 2 λ`
  (the least `D` with `λ ≤ 2^D`, equal to `⌈log₂ λ⌉` for `λ ≥ 1`); `[Δ] = Fin Δ`;
  `⌈√n⌉ = Nat.ceil (Real.sqrt n)`; `c_q = ⌈2 log_Δ q⌉` (real logarithm; `c_0 = c_1 = 0`).
* **Indexing.** `tl λ i` is the paper's `λ^{(i+1)}`: `tl λ 0 = λ^{(1)} = λ` and
  `tl λ (i+1) = ⌈√(tl λ i)⌉`. Paper level `i ∈ [ℓ]` is level `k = i − 1` here: it maps the state
  `y^{(i)}` (length `tl λ k`) to `y^{(i+1)} = G_{λ^{(i)}}(y^{(i)}, r^{(i)}_{x̃_i})` (length
  `tl λ (k+1)`), the state being the **key** of `G` and the pool element its **input**.
* The building blocks are an argument: `G n : {0,1}^{p(n)} → {0,1}^{⌈√n⌉}` with key `{0,1}^n`,
  and a hash `H_λ` with key `{0,1}^{kh(λ)}` into `[Δ]^ℓ`. `[Δ]^ℓ` is represented as `ℓ` blocks of
  `log Δ` bits (`ℓ · log Δ` output bits), block `k` read as the binary number
  `∑_t b_{k,t} 2^t ∈ Fin Δ` (`blockIdx`), as in the proof of Lemma 4.5.
* The construction is defined, by the same formulas, at every `λ` (no separate small-`λ` branch
  is needed for the definitions to make sense; statements that need `λ` large say so, e.g. by
  `c_q < ℓ`).
* One tree's key is `(k_G, k_XG, k_H)`; `ℱ′_λ = ℱ_λ^{⊕m}` has key `(Fin m → TreeKey)` and output
  the XOR (Definition 3.8). For the ensemble `constrEnsemble`, the key is a bit string of length
  `keyLen λ = m·(λ + ∑_{k<ℓ} Δ·p(λ^{(k+1)}) + kh(λ))`: the key bits are indexed by
  `KeyIdx λ = Fin m × (Fin λ ⊕ (Σ k, Fin Δ × Fin p(λ^{(k+1)})) ⊕ Fin kh(λ))` through a fixed
  bijection `Fintype.equivFin`. The decoding only permutes bit positions, so it costs no gates
  and maps uniform bit strings to uniform keys.
-/

/-- `⌈√n⌉`. -/
noncomputable def ceilSqrt (n : ℕ) : ℕ := ⌈Real.sqrt n⌉₊

/-- `ℓ = ⌈log log log λ⌉` (base 2). -/
noncomputable def ell (lam : ℕ) : ℕ := ⌈Real.logb 2 (Real.logb 2 (Real.logb 2 lam))⌉₊

/-- `log Δ = ⌈log₂ λ⌉ = Nat.clog 2 λ`. -/
def logDelta (lam : ℕ) : ℕ := Nat.clog 2 lam

/-- `Δ = 2^{⌈log λ⌉}`. -/
def Delta (lam : ℕ) : ℕ := 2 ^ logDelta lam

/-- `tl λ i = λ^{(i+1)}`: `λ^{(1)} = λ`, `λ^{(i+1)} = ⌈√(λ^{(i)})⌉`. -/
noncomputable def tl (lam : ℕ) : ℕ → ℕ
  | 0 => lam
  | i + 1 => ceilSqrt (tl lam i)

/-- `c_q = ⌈2 log_Δ q⌉`. -/
noncomputable def cq (q lam : ℕ) : ℕ := ⌈2 * Real.logb (Delta lam) q⌉₊

/-- Block `k` of `L · D` bits read as the binary number `∑_t b_{k,t} 2^t ∈ Fin (2^D)`. -/
def blockIdx {L D : ℕ} (z : Fin (L * D) → Bool) (k : Fin L) : Fin (2 ^ D) :=
  finFunctionFinEquiv (fun t : Fin D => if z (finProdFinEquiv (k, t)) then 1 else 0)

/-- The input pool `k_XG = {(r^{(i)}_1, …, r^{(i)}_Δ)}_{i ∈ [ℓ]}`, with `r^{(i)}_j` of `p(λ^{(i)})`
bits (level `k = i − 1`). -/
abbrev Pool (p : ℕ → ℕ) (lam : ℕ) : Type :=
  (k : Fin (ell lam)) → Fin (Delta lam) → Fin (p (tl lam k)) → Bool

/-- One level of TGGM: at level `k < ℓ`, `y ↦ G_{λ^{(k+1)}}(y, r^{(k+1)}_{x̃_{k+1}})`. -/
noncomputable def levelStep {p : ℕ → ℕ} (G : (n : ℕ) → FunFam (Fin n → Bool) (p n) (ceilSqrt n))
    {lam : ℕ} (pool : Pool p lam) (xt : Fin (ell lam) → Fin (Delta lam)) (k : ℕ)
    (y : Fin (tl lam k) → Bool) : Fin (tl lam (k + 1)) → Bool :=
  if hk : k < ell lam then G (tl lam k) y (pool ⟨k, hk⟩ (xt ⟨k, hk⟩)) else fun _ => false

/-- Run the levels `i, i+1, …, L−1` on the state `y` at level `i`, returning the state at level
`L` (`fun _ => false` if `i > L`, a case never used). -/
noncomputable def runTo {lam : ℕ} (L : ℕ)
    (step : (k : ℕ) → (Fin (tl lam k) → Bool) → (Fin (tl lam (k + 1)) → Bool)) :
    (i : ℕ) → (Fin (tl lam i) → Bool) → (Fin (tl lam L) → Bool)
  | i, y =>
    if _h : i < L then runTo L step (i + 1) (step i y)
    else if h' : i = L then h' ▸ y else fun _ => false
termination_by i => L - i

/-- A key `k_F = (k_G, k_XG, k_H)` for one tapered tree. -/
abbrev TreeKey (p : ℕ → ℕ) (kh : ℕ → ℕ) (lam : ℕ) : Type :=
  (Fin lam → Bool) × Pool p lam × (Fin (kh lam) → Bool)

/-- One tapered tree `ℱ_λ`: `F_{k_F}(x) = TGGM(H_{k_H}(x))`, output `λ^{(ℓ+1)} = tl λ ℓ` bits. -/
noncomputable def treeFam {p : ℕ → ℕ} (G : (n : ℕ) → FunFam (Fin n → Bool) (p n) (ceilSqrt n))
    {kh : ℕ → ℕ} (H : (lam : ℕ) → FunFam (Fin (kh lam) → Bool) lam (ell lam * logDelta lam))
    (lam : ℕ) : FunFam (TreeKey p kh lam) lam (tl lam (ell lam)) :=
  fun key x =>
    runTo (ell lam) (levelStep G key.2.1 (fun k => blockIdx (H lam key.2.2 x) k)) 0 key.1

/-- `ℱ′_λ = ℱ_λ^{⊕m}` with `m = λ` (keys as `m` tree keys). -/
noncomputable def constrFam {p : ℕ → ℕ} (G : (n : ℕ) → FunFam (Fin n → Bool) (p n) (ceilSqrt n))
    {kh : ℕ → ℕ} (H : (lam : ℕ) → FunFam (Fin (kh lam) → Bool) lam (ell lam * logDelta lam))
    (lam : ℕ) : FunFam (Fin lam → TreeKey p kh lam) lam (tl lam (ell lam)) :=
  sumPow (treeFam G H lam) lam

/-- Positions of the key bits of `ℱ′_λ`: tree, then `k_G` bit, pool bit, or `k_H` bit. -/
abbrev KeyIdx (p : ℕ → ℕ) (kh : ℕ → ℕ) (lam : ℕ) : Type :=
  Fin lam × (Fin lam ⊕ ((k : Fin (ell lam)) × Fin (Delta lam) × Fin (p (tl lam k))) ⊕ Fin (kh lam))

/-- Key length of `ℱ′_λ` as a bit string. -/
noncomputable def keyLen (p : ℕ → ℕ) (kh : ℕ → ℕ) (lam : ℕ) : ℕ := Fintype.card (KeyIdx p kh lam)

/-- Decode a key bit string of `ℱ′_λ` into `m` tree keys (a permutation of bit positions). -/
noncomputable def decodeKey (p : ℕ → ℕ) (kh : ℕ → ℕ) (lam : ℕ) (z : Fin (keyLen p kh lam) → Bool) :
    Fin lam → TreeKey p kh lam :=
  fun i =>
    (fun a => z (Fintype.equivFin (KeyIdx p kh lam) (i, .inl a)),
     fun k j b => z (Fintype.equivFin (KeyIdx p kh lam) (i, .inr (.inl ⟨k, j, b⟩))),
     fun c => z (Fintype.equivFin (KeyIdx p kh lam) (i, .inr (.inr c))))

/-- Construction 4.3 as a function family ensemble: input length `λ`, output length
`λ^{(ℓ+1)}`, key length `keyLen λ`. -/
noncomputable def constrEnsemble {p : ℕ → ℕ}
    (G : (n : ℕ) → FunFam (Fin n → Bool) (p n) (ceilSqrt n)) {kh : ℕ → ℕ}
    (H : (lam : ℕ) → FunFam (Fin (kh lam) → Bool) lam (ell lam * logDelta lam)) : Ensemble where
  p0 := fun lam => lam
  p1 := fun lam => tl lam (ell lam)
  p2 := keyLen p kh
  F := fun lam z x => constrFam G H lam (decodeKey p kh lam z) x

end LowDepthPRF


