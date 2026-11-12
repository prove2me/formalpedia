-- Prove2me | Definitions.Def_ImpuritySim_BandwiseForm
-- name    : ImpuritySim_BandwiseForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:31:35.709128+00:00
-- url     : https://prove2.me/theorems/885ebaaf-af02-4aa3-abfe-e9bb87e953dc
-- title:
--   The bandwise hybridization form with enlarged impurity (3.15) and the quantities $\xi_\ell,\kappa,\chi$ (3.16)–(3.18)
-- statement:
--   After preprocessing (App. A) and the bandwise Krylov construction (§3), an impurity Hamiltonian on $n$ modes takes the **bandwise hybridization form with enlarged impurity**
--   $$H=K+\Phi(E)+\sum_{\ell=0}^{L}\sum_{s=1}^{r_\ell}\bigl(a^\dagger(u_{\ell s})G_{\ell s}+G_{\ell s}^\dagger a(u_{\ell s})\bigr),\qquad(3.15)$$
--   written in the bandwise Krylov basis viewed as the standard basis. This file records the data and properties of that form:
--
--   1. the impurity size $m\ge1$ and energies $0<\omega\le J$; $L=\lceil\log_2(J/\omega)\rceil$ and $\omega_\ell=2^\ell\omega$ (3.9);
--   2. the set of **residual-bath modes** $a_i$ (the others are the enlarged-impurity modes $b_k$), each with a band $\ell(i)\le L$ and a Krylov depth $d(i)\ge1$; at most $2m$ bath modes in each band and depth (Lemma 3.1) and at most $m+2m(L+1)$ enlarged-impurity modes;
--   3. a Hermitian $E=\bigoplus_\ell E_\ell$ acting on the residual bath, block-diagonal over bands and block-tridiagonal in depth, with $\omega_\ell I\le E_\ell\le2\omega_\ell I$;
--   4. for each band, $r_\ell\le2m$ orthonormal vectors $u_{\ell s}$ in the depth-$1$ shell of band $\ell$, and operators $G_{\ell s}=\sigma_{\ell s}b(v_{\ell s})$, linear combinations of enlarged-impurity annihilators with $\|G_{\ell s}\|\le2\omega_\ell$;
--   5. an even Hermitian term $K=\sum_Ak_A\Gamma_A$ ($k_A$ real) acting only on the enlarged impurity.
--
--   The quantities controlling the complexity are
--   $$\xi_\ell=\Bigl\|\sum_{s=1}^{r_\ell}G_{\ell s}^\dagger G_{\ell s}\Bigr\|\ (3.16),\qquad \kappa=\sum_{\ell=0}^L\frac{\xi_\ell}{\omega_\ell^2}\ (3.17),\qquad \chi=\#\{\text{enlarged-impurity modes}\}+\max_{d\ge1}\#\{\text{bath modes at depth }d\}\ (3.18).$$
--
--   Every result of §§3–5 is stated for a Hamiltonian in this form.
--
--   **Formalization Note** $G_{\ell s}=a(g_{\ell s})$ with $g_{\ell s}$ supported off the bath and $\|g_{\ell s}\|\le2\omega_\ell$, which is $\sigma_{\ell s}b(v_{\ell s})$ with $|\sigma_{\ell s}|\le2\omega_\ell$. Majorana $p$ ($0$-based) belongs to mode $\lfloor p/2\rfloor$. The bounds $\omega_\ell I\le E_\ell\le2\omega_\ell I$ are quadratic-form bounds on vectors supported on the band-$\ell$ bath modes. The structure carries the properties, not the construction: the milestones hold for every data with these properties.
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), (3.9), p.16; (3.12)–(3.14), pp.16–17; (3.15)–(3.18), p.18; Lemma 3.1, p.15; mode order p.19; ℓ(i), d(i), p.20

import Mathlib
import Definitions.Def_ImpuritySim_Fermion

open Matrix

namespace ImpuritySim

/-!
# The bandwise hybridization form with enlarged impurity (3.15)–(3.18)

J. Jiang, N. Ju, O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation
of quantum impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2): (3.9),
p.16; (3.12)–(3.14), pp.16–17; (3.15)–(3.18), p.18; Lemma 3.1, p.15; the mode order of p.19 and
the band/depth labels `ℓ(i)`, `d(i)` of p.20.

**Formalization Note.**
* §§3–5 state their results for an impurity Hamiltonian "in the form given in Eq. (3.15)", written
  in the bandwise Krylov basis viewed as the standard basis (p.17). `BandwiseForm n` records exactly
  the data and properties of that form on `n` modes (`Fin n`, 0-based), in that basis:
  - `bath` is the set of residual-bath modes `a_i`; the other modes are the enlarged-impurity
    modes `b_k`. Each bath mode `i` has a band `band i = ℓ(i) ≤ L` and a depth
    `depth i = d(i) ≥ 1` (its basis vector lies in `W_{ℓ(i), d(i)}`).
  - `L = numBands ω J = ⌈log₂(J/ω)⌉` (3.9), `ω_ℓ = 2^ℓ ω` (`omegaL`), `0 < ω ≤ J`, `m ≥ 1`.
  - Shell sizes: at most `2m` bath modes per band and depth (Lemma 3.1, `dim W_{ℓ,d} ≤ 2m`); at most
    `m + 2m(L+1)` enlarged-impurity modes (`dim(W_imp ⊕ ⊕_ℓ W_{ℓ0})`). Together these give (3.18),
    `χ ≤ m + 4m(L+1)`.
  - `E` is Hermitian and supported on bath × bath, within one band (`E = ⊕_ℓ E_ℓ`) and between
    depths differing by at most one (block-tridiagonal, (3.2), (3.21)); on every band `ℓ ≤ L`,
    `ω_ℓ I ≤ E_ℓ ≤ 2ω_ℓ I` (as quadratic forms on vectors supported on the band-`ℓ` bath modes).
  - `u ℓ s` (`s < r_ℓ ≤ 2m`) are orthonormal vectors supported on the band-`ℓ`, depth-1 bath modes
    (`u_{ℓs} ∈ W_{ℓ1}`); `G ℓ s = a(g ℓ s)` with `g ℓ s` supported off the bath and `‖g ℓ s‖ ≤ 2ω_ℓ`,
    i.e. `G_{ℓs} = σ_{ℓs} b(v_{ℓs})` with `|σ_{ℓs}| ≤ 2ω_ℓ` ((3.13)–(3.15)).
  - `K = Σ_A k_A Γ_A` with real `k_A`, nonzero only for even sets `A` of Majoranas of non-bath
    modes (Majorana `p` belongs to mode `⌊p/2⌋`): `K` is even and acts on the enlarged impurity
    only. Every even Hermitian operator on the enlarged-impurity modes has this form.
* `H F = K + Φ(E) + Σ_{ℓ ≤ L} Σ_s (a†(u_{ℓs}) G_{ℓs} + G_{ℓs}† a(u_{ℓs}))` (3.15), with
  `a†(u) = a(u)†`.
* `xi F ℓ = ‖Σ_s G_{ℓs}† G_{ℓs}‖` (3.16, spectral norm), `kappa F = Σ_{ℓ ≤ L} ξ_ℓ / ω_ℓ²` (3.17),
  `chi F = #(non-bath modes) + max_{d ≥ 1} #{bath modes at depth d}` (3.18).
* Every form produced by the paper's construction (App. A, §3) has these properties; the
  milestones hold for every data with these properties.
-/

open FermiCap.Gaussian

/-- The number of the last band, `L = ⌈log₂(J/ω)⌉` (3.9). -/
noncomputable def numBands (ω J : ℝ) : ℕ := ⌈Real.logb 2 (J / ω)⌉₊

/-- An impurity Hamiltonian on `n` modes in the bandwise hybridization form with enlarged impurity
(3.15), in the bandwise Krylov basis, with the properties (3.15)–(3.18) and Lemma 3.1 give. -/
structure BandwiseForm (n : ℕ) where
  /-- The impurity size `m ≥ 1`. -/
  m : ℕ
  one_le_m : 1 ≤ m
  /-- The lower bound `ω` on the bath single-particle energies (2.15). -/
  ω : ℝ
  /-- The upper bound `J` on the bath single-particle energies (2.12), (2.15). -/
  J : ℝ
  ω_pos : 0 < ω
  ω_le_J : ω ≤ J
  /-- The residual-bath modes. -/
  bath : Finset (Fin n)
  /-- The band `ℓ(i)` of a residual-bath mode. -/
  band : Fin n → ℕ
  /-- The Krylov depth `d(i)` of a residual-bath mode. -/
  depth : Fin n → ℕ
  band_le : ∀ i ∈ bath, band i ≤ numBands ω J
  one_le_depth : ∀ i ∈ bath, 1 ≤ depth i
  /-- `dim W_{ℓ,d} ≤ 2m` (Lemma 3.1). -/
  shell_card : ∀ ℓ d : ℕ, (bath.filter fun i => band i = ℓ ∧ depth i = d).card ≤ 2 * m
  /-- `dim(W_imp ⊕ ⊕_ℓ W_{ℓ0}) ≤ m + 2m(L+1)`. -/
  imp_card : (Finset.univ \ bath).card ≤ m + 2 * m * (numBands ω J + 1)
  /-- The residual-bath matrix `E = ⊕_ℓ E_ℓ`. -/
  E : Matrix (Fin n) (Fin n) ℂ
  E_herm : E.IsHermitian
  E_supp : ∀ i j, E i j ≠ 0 →
    i ∈ bath ∧ j ∈ bath ∧ band i = band j ∧ depth i ≤ depth j + 1 ∧ depth j ≤ depth i + 1
  /-- `ω_ℓ I ≤ E_ℓ`. -/
  E_lower : ∀ ℓ ≤ numBands ω J, ∀ v : Fin n → ℂ, (∀ i, v i ≠ 0 → i ∈ bath ∧ band i = ℓ) →
    2 ^ ℓ * ω * (star v ⬝ᵥ v).re ≤ (star v ⬝ᵥ (E *ᵥ v)).re
  /-- `E_ℓ ≤ 2ω_ℓ I`. -/
  E_upper : ∀ ℓ ≤ numBands ω J, ∀ v : Fin n → ℂ, (∀ i, v i ≠ 0 → i ∈ bath ∧ band i = ℓ) →
    (star v ⬝ᵥ (E *ᵥ v)).re ≤ 2 * (2 ^ ℓ * ω) * (star v ⬝ᵥ v).re
  /-- The number `r_ℓ ≤ 2m` of hybridization terms in band `ℓ`. -/
  r : ℕ → ℕ
  r_le : ∀ ℓ, r ℓ ≤ 2 * m
  /-- The vectors `u_{ℓs}`. -/
  u : (ℓ : ℕ) → Fin (r ℓ) → Fin n → ℂ
  u_orthonormal : ∀ ℓ (s t : Fin (r ℓ)), star (u ℓ s) ⬝ᵥ u ℓ t = if s = t then 1 else 0
  u_supp : ∀ ℓ s i, u ℓ s i ≠ 0 → i ∈ bath ∧ band i = ℓ ∧ depth i = 1
  /-- The vectors `σ_{ℓs} v_{ℓs}` on the enlarged impurity, so that `G_{ℓs} = a(g ℓ s)`. -/
  g : (ℓ : ℕ) → Fin (r ℓ) → Fin n → ℂ
  g_supp : ∀ ℓ s i, g ℓ s i ≠ 0 → i ∉ bath
  g_norm : ∀ ℓ s, (star (g ℓ s) ⬝ᵥ g ℓ s).re ≤ (2 * (2 ^ ℓ * ω)) ^ 2
  /-- The Majorana coefficients of the enlarged-impurity term `K`. -/
  k : Finset (Fin (2 * n)) → ℝ
  k_supp : ∀ A, k A ≠ 0 → Even A.card ∧ ∀ p ∈ A, (⟨p.val / 2, by omega⟩ : Fin n) ∉ bath

namespace BandwiseForm

variable {n : ℕ} (F : BandwiseForm n)

/-- `L = ⌈log₂(J/ω)⌉` (3.9). -/
noncomputable def L : ℕ := numBands F.ω F.J

/-- `ω_ℓ = 2^ℓ ω` (3.9). -/
noncomputable def omegaL (ℓ : ℕ) : ℝ := 2 ^ ℓ * F.ω

/-- `G_{ℓs} = σ_{ℓs} b(v_{ℓs}) = a(g ℓ s)`. -/
noncomputable def G (ℓ : ℕ) (s : Fin (F.r ℓ)) : Op n := annVec n (F.g ℓ s)

/-- The enlarged-impurity term `K = Σ_A k_A Γ_A`. -/
noncomputable def K : Op n := ∑ A, ((F.k A : ℝ) : ℂ) • majMono n A

/-- The Hamiltonian (3.15): `H = K + Φ(E) + Σ_{ℓ ≤ L} Σ_s (a†(u_{ℓs}) G_{ℓs} + G_{ℓs}† a(u_{ℓs}))`. -/
noncomputable def H : Op n :=
  F.K + Phi n F.E + ∑ ℓ ∈ Finset.range (F.L + 1), ∑ s : Fin (F.r ℓ),
    ((annVec n (F.u ℓ s))ᴴ * F.G ℓ s + (F.G ℓ s)ᴴ * annVec n (F.u ℓ s))

/-- `ξ_ℓ = ‖Σ_s G_{ℓs}† G_{ℓs}‖` (3.16). -/
noncomputable def xi (ℓ : ℕ) : ℝ := specNorm (∑ s : Fin (F.r ℓ), (F.G ℓ s)ᴴ * F.G ℓ s)

/-- `κ = Σ_{ℓ=0}^{L} ξ_ℓ / ω_ℓ²` (3.17). -/
noncomputable def kappa : ℝ := ∑ ℓ ∈ Finset.range (F.L + 1), F.xi ℓ / F.omegaL ℓ ^ 2

/-- `χ = #(enlarged-impurity modes) + max_{d ≥ 1} #{bath modes at depth d}` (3.18). -/
def chi : ℕ :=
  (Finset.univ \ F.bath).card +
    (F.bath.image F.depth).sup fun d => (F.bath.filter fun i => F.depth i = d).card

/-- The band-`ℓ` residual-bath modes. -/
abbrev bandIdx (ℓ : ℕ) := {i : Fin n // i ∈ F.bath ∧ F.band i = ℓ}

/-- The band block `E_ℓ` of `E`, on the band-`ℓ` residual-bath modes. -/
def Eband (ℓ : ℕ) : Matrix (F.bandIdx ℓ) (F.bandIdx ℓ) ℂ :=
  F.E.submatrix Subtype.val Subtype.val

end BandwiseForm

end ImpuritySim


