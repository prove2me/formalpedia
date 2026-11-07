-- Prove2me | Definitions.Def_Z2PostSamp_Construction
-- name    : Z2PostSamp_Construction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:47.738999+00:00
-- url     : https://prove2.me/theorems/dd0f3288-7c1d-40f5-9845-2b943a0ba924
-- title:
--   The exact construction of §2.3: tuning record, stored centre $v$, orientation $v^+$, checkpoint centres and the domains $\mathcal K_k$
-- statement:
--   A **tuning record** consists of integers $M,L_{\mathrm{init}},L_0,\dots,L_{M-1}\ge1$, a step size $\gamma\in(0,1)$, radii $\rho_0,\rho>0$ and fractions $0<\alpha_0<\dots<\alpha_M<1$; put $j_\ell=\lfloor\alpha_\ell n\rfloor$, $c_n=1-2^{-n}$ and $D_{R,n}=[-c_n,c_n]^R$.
--
--   1. **Stored centre.** Take an eigenvector of the largest eigenvalue of $J$, with a deterministic sign, normalized to $\|z^0\|^2=n\lambda^2(\lambda^2-1)$; set $u^{-1}=\lambda z^0$ and run $u^\ell=\tanh z^\ell$, $z^{\ell+1}=Ju^\ell-\lambda^2(1-\|u^\ell\|^2/n)u^{\ell-1}$ for $0\le\ell<L_{\mathrm{init}}$; then $n$ updates $z\leftarrow(1-\gamma)z+\gamma\{Ju-\lambda^2(1-\|u\|^2/n)u\}$, $u=\tanh z$; finally $v=\mathrm{Proj}_{D_{[n],n}}(\tanh z)$.
--   2. **Orientation.** $v^+(x_{S_{k_0}})=\operatorname{sign}\big(\sum_{a\le k_0}x_{I_a}v_{I_a}\big)\,v$ with $\operatorname{sign}(0)=0$.
--   3. **Checkpoints.** At $j=j_\ell$, with $N=n-j$ and $r=r_{j/n}$: $z^0=h^{(j)}(x_{S_j})$, $u^{-1}=0$, $u^t=\tanh z^t$, $z^{t+1}=J_{R_j,R_j}u^t+h^{(j)}-r(1-\|u^t\|^2/N)u^{t-1}$ for $0\le t<L_\ell$, and $v^{(j)}=\mathrm{Proj}_{D_{R_j,n}}(\tanh z^{L_\ell})$.
--   4. **Domains.**
--   $$\mathcal K_k(x_{S_k})=\begin{cases}D_{R_k,n}\cap B(v^+|_{R_k},\rho_0\sqrt n), & k_0\le k<j_0,\\ D_{R_k,n}\cap B(v^{(j_\ell)}|_{R_k},\rho\sqrt n), & j_\ell\le k<j_{\ell+1},\\ D_{R_k,n}, & k\ge j_M.\end{cases}$$
--
--   These are the exact-arithmetic objects of the sampler; the numerical routines of the appendices only add tolerances.
--
--   **Formalization Note** A vector on $R_k$ is a vector of `Fin n → ℝ` vanishing on $S_k$. The projection onto a box is the coordinatewise clamp. The eigenvector is a fixed choice (`Classical.choose`) of a unit maximizer of $v^\top Jv$ with $Jv=(v^\top Jv)v$ (zero if none exists); the orientation removes its sign. Only the first $M$ (resp. $M+1$) values of the record's sequences are read. For $k<k_0$ the first case is used; no statement reads it.
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), §2.3, pp.10–11, (2.12)–(2.15)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_Z2PostSamp_RevealPath
import Definitions.Def_Z2PostSamp_Scalars

set_option autoImplicit false

open OAI.CriticalSK Matrix

namespace Z2PostSamp

noncomputable section

/-!
# The exact-arithmetic construction of §2.3: stored centre, checkpoint centres, domains `𝒦_k`

Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), §2.3, pp.10–11. A tuning record consists of integers `M, L_init, L_0, …,
L_{M−1} ≥ 1`, a step size `γ ∈ (0,1)`, radii `ρ₀, ρ > 0` and fractions `0 < α₀ < ⋯ < α_M < 1`;
`j_ℓ = ⌊α_ℓ n⌋`, `c_n = 1 − 2^{−n}`, `D_{R,n} = [−c_n, c_n]^R`. For the fixed record: a deterministic
eigenvector of the largest eigenvalue of `J`, normalized to `z⁰` with `‖z⁰‖² = nλ²(λ² − 1)`;
`u^{−1} = λz⁰` and the spectral AMP (2.12) `u^ℓ = tanh z^ℓ`,
`z^{ℓ+1} = J u^ℓ − λ²(1 − ‖u^ℓ‖²/n) u^{ℓ−1}` for `0 ≤ ℓ < L_init`; then `n` natural-gradient updates
`u = tanh z`, `z ← (1 − γ) z + γ{J u − λ²(1 − ‖u‖²/n) u}`; `v = Proj_{D_{[n],n}}(tanh z)`;
(2.13) `v⁺(x_{S_{k₀}}) = sign(Σ_{a ≤ k₀} x_{I_a} v_{I_a}) v`, `sign(0) = 0`; at a checkpoint
`j = j_ℓ`, `N = n − j`, `r = r_{j/n}`, (2.14) `z⁰ = ĥ^{(j)}`, `u^{−1} = 0`, `u^t = tanh z^t`,
`z^{t+1} = J_{R_j,R_j} u^t + ĥ^{(j)} − r(1 − ‖u^t‖²/N) u^{t−1}` for `0 ≤ t < L_ℓ`,
`v^{(j)} = Proj_{D_{R_j,n}}(tanh z^{L_ℓ})`; and the domains (2.15)
`𝒦_k = D_{R_k,n} ∩ B(v⁺|_{R_k}, ρ₀√n)` for `k₀ ≤ k < j₀`,
`D_{R_k,n} ∩ B(v^{(j_ℓ)}|_{R_k}, ρ√n)` for `j_ℓ ≤ k < j_{ℓ+1}`, `D_{R_k,n}` for `k ≥ j_M`.

**Formalization Note.** This is the exact-arithmetic construction, the paper's analytic object
(App. A–B add numerical tolerances only). Vectors are `Fin n → ℝ`, norms Euclidean; a vector on
`R_k` is a vector of `Fin n → ℝ` vanishing on `S_k`, so `𝒦_k` is a subset of `Fin n → ℝ` whose points
vanish off `R_k`. The Euclidean projection onto the box `[−c_n, c_n]^R` is the coordinatewise clamp.
"A deterministic sign for an eigenvector of the largest eigenvalue" is a fixed choice
(`Classical.choose`) of a unit vector `v` with `J v = (vᵀJv) v` maximizing `vᵀJv` over the unit
sphere (for symmetric `J`, a unit eigenvector of `λ_max`; the zero vector if none exists, e.g. at
`n = 0`); the orientation (2.13) removes the sign. The record's sequences are functions on `ℕ` of
which only the first `M` (`L`) or `M + 1` (`α`) values are read. For `k < k₀` the first case of
(2.15) is used; no statement reads it. The safeguards of App. A (uniform fallback) are not part of
the exact construction.
-/

/-- `c_n = 1 − 2^{−n}` (p.10). -/
def cn (n : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ n

/-- The squared Euclidean norm `‖v‖²`. -/
def sqNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Coordinatewise `tanh`. -/
def tanhV {n : ℕ} (z : Fin n → ℝ) : Fin n → ℝ := fun i => Real.tanh (z i)

/-- The Euclidean projection onto the box `[−c, c]ⁿ`: the coordinatewise clamp. -/
def clipVec {n : ℕ} (c : ℝ) (v : Fin n → ℝ) : Fin n → ℝ := fun i => max (-c) (min c (v i))

/-- `v` is a unit eigenvector of the largest eigenvalue of `J` (Rayleigh-quotient maximizer). -/
def IsTopEigvec {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : Prop :=
  sqNorm v = 1 ∧ (∀ w : Fin n → ℝ, sqNorm w = 1 → w ⬝ᵥ (J *ᵥ w) ≤ v ⬝ᵥ (J *ᵥ v)) ∧
    J *ᵥ v = (v ⬝ᵥ (J *ᵥ v)) • v

open Classical in
/-- The fixed choice of a unit top eigenvector of `J` (zero if none exists). -/
def topEig {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  if h : ∃ v, IsTopEigvec J v then Classical.choose h else 0

/-- `z⁰`, the top eigenvector normalized to `‖z⁰‖² = nλ²(λ² − 1)` (p.10). -/
def zInit {n : ℕ} (lam : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  Real.sqrt (n * lam ^ 2 * (lam ^ 2 - 1)) • topEig J

/-- One step `(z^ℓ, u^{ℓ−1}) ↦ (z^{ℓ+1}, u^ℓ)` of the spectral AMP (2.12). -/
def ampStep {n : ℕ} (lam : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (J *ᵥ tanhV p.1 - (lam ^ 2 * (1 - sqNorm (tanhV p.1) / n)) • p.2, tanhV p.1)

/-- `z^{L_init}` of (2.12), from `z⁰` and `u^{−1} = λ z⁰`. -/
def ampOut {n : ℕ} (lam : ℝ) (Linit : ℕ) (J : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  ((ampStep lam J)^[Linit] (zInit lam J, lam • zInit lam J)).1

/-- One natural-gradient update `z ← (1 − γ)z + γ{J u − λ²(1 − ‖u‖²/n) u}`, `u = tanh z` (p.11). -/
def natStep {n : ℕ} (lam γ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  (1 - γ) • z + γ • (J *ᵥ tanhV z - (lam ^ 2 * (1 - sqNorm (tanhV z) / n)) • tanhV z)

/-- The stored vector `v = Proj_{D_{[n],n}}(tanh z)` after `L_init` AMP steps and `n` natural-gradient
updates (p.11). -/
def storedV {n : ℕ} (lam : ℝ) (Linit : ℕ) (γ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  clipVec (cn n) (tanhV ((natStep lam γ J)^[n] (ampOut lam Linit J)))

/-- A tuning record (p.10). -/
structure TuningRecord where
  /-- The number `M` of checkpoints. -/
  M : ℕ
  /-- The number `L_init` of spectral AMP steps. -/
  Linit : ℕ
  /-- The AMP counts `L_0, …, L_{M−1}` at the checkpoints. -/
  L : ℕ → ℕ
  /-- The natural-gradient step size `γ`. -/
  γ : ℝ
  /-- The initial radius `ρ₀`. -/
  ρ0 : ℝ
  /-- The checkpoint radius `ρ`. -/
  ρ : ℝ
  /-- The fractions `α_0, …, α_M`. -/
  α : ℕ → ℝ

/-- Validity of a record: `M, L_init, L_0, …, L_{M−1} ≥ 1`, `γ ∈ (0,1)`, `ρ₀, ρ > 0`,
`0 < α₀ < ⋯ < α_M < 1` (p.10). -/
def TuningRecord.Valid (rec : TuningRecord) : Prop :=
  1 ≤ rec.M ∧ 1 ≤ rec.Linit ∧ (∀ ℓ < rec.M, 1 ≤ rec.L ℓ) ∧ 0 < rec.γ ∧ rec.γ < 1 ∧
    0 < rec.ρ0 ∧ 0 < rec.ρ ∧ 0 < rec.α 0 ∧ (∀ ℓ < rec.M, rec.α ℓ < rec.α (ℓ + 1)) ∧
    rec.α rec.M < 1

/-- The checkpoint index `j_ℓ = ⌊α_ℓ n⌋` (p.10). -/
def jIdx (rec : TuningRecord) (n ℓ : ℕ) : ℕ := ⌊rec.α ℓ * n⌋₊

/-- The orientation (2.13): `v⁺(x_{S_{k₀}}) = sign(Σ_{a ≤ k₀} x_{I_a} v_{I_a}) v`, `sign 0 = 0`. -/
def vplus {n : ℕ} (lam : ℝ) (rec : TuningRecord) (J : Matrix (Fin n) (Fin n) ℝ)
    (I : Equiv.Perm (Fin n)) (x : Spin n) : Fin n → ℝ :=
  Real.sign (∑ a : Fin n, if a.val < k0 n lam then
      spinValue (x (I a)) * storedV lam rec.Linit rec.γ J (I a) else 0) •
    storedV lam rec.Linit rec.γ J

/-- One step `(z^t, u^{t−1}) ↦ (z^{t+1}, u^t)` of the checkpoint AMP (2.14) at checkpoint `j`, on
`R_j` (zero on `S_j`). -/
def chkStep {n : ℕ} (lam : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n)) (x : Spin n)
    (j : ℕ) (p : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  let u := onR I j (tanhV p.1)
  (onR I j (J *ᵥ u + field J I x j) -
      (rAl lam ((j : ℝ) / n) * (1 - sqNorm u / ((n : ℝ) - j))) • p.2, u)

/-- The checkpoint centre `v^{(j_ℓ)}(x_{S_{j_ℓ}}) = Proj_{D_{R_j,n}}(tanh z^{L_ℓ})` of (2.14),
`j = j_ℓ`, started at `z⁰ = ĥ^{(j)}`, `u^{−1} = 0`. -/
def chkV {n : ℕ} (lam : ℝ) (rec : TuningRecord) (J : Matrix (Fin n) (Fin n) ℝ)
    (I : Equiv.Perm (Fin n)) (x : Spin n) (ℓ : ℕ) : Fin n → ℝ :=
  let j := jIdx rec n ℓ
  onR I j (clipVec (cn n)
    (tanhV ((chkStep lam J I x j)^[rec.L ℓ] (onR I j (field J I x j), 0)).1))

open Classical in
/-- The domain `𝒦_k(x_{S_k})` of (2.15), as a set of vectors vanishing off `R_k`. -/
def Kdom {n : ℕ} (lam : ℝ) (rec : TuningRecord) (J : Matrix (Fin n) (Fin n) ℝ)
    (I : Equiv.Perm (Fin n)) (x : Spin n) (k : ℕ) : Set (Fin n → ℝ) :=
  {u | (∀ i, i ∉ Rset I k → u i = 0) ∧ (∀ i ∈ Rset I k, |u i| ≤ cn n) ∧
    (if k < jIdx rec n 0 then
      ∑ i ∈ Rset I k, (u i - vplus lam rec J I x i) ^ 2 ≤ rec.ρ0 ^ 2 * n
    else if k < jIdx rec n rec.M then
      ∑ i ∈ Rset I k, (u i - chkV lam rec J I x
        (Nat.findGreatest (fun ℓ => jIdx rec n ℓ ≤ k) (rec.M - 1)) i) ^ 2 ≤ rec.ρ ^ 2 * n
    else True)}

end

end Z2PostSamp


