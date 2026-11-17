-- Prove2me | Definitions.Def_BilatMatch_Supplement_marketTarget
-- name    : BilatMatch_Supplement_marketTarget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:28:12.085147+00:00
-- url     : https://prove2.me/theorems/7212f918-7bed-492e-bd27-458349b07c3c
-- title:
--   Bilateral targets $B^r_\ell$, $\beta_r$, envelope targets (26), and the market-level benchmark $T_\alpha(\mathcal I)$
-- statement:
--   Fix a matching market $\mathcal I$ with finitely many agents and finitely supported priors, and a canonical first-best matching $M^*$ (fewest edges among maximum-GFT matchings, a fixed tie order).
--
--   For a seller with costs $c_1<\dots<c_m$ and masses $f_S(c_k)>0$, put $\kappa_r=\{c_1,\dots,c_r\}$ and, for a buyer value $v_\ell$,
--   $$B^r_\ell=\sum_{k\le r}f_S(c_k)(v_\ell-c_k)_+ .$$
--   For a buyer support $v_1<\dots<v_n$,
--   $$\beta_r=\inf_{F_B}\frac{V_\alpha(F_B,F_S^{\kappa_r})}{\mathrm{FB}(F_B,F_S^{\kappa_r})}\qquad(25)$$
--   over buyer priors with support $\{v_1,\dots,v_n\}$, and the **envelope targets** are
--   $$T^r_\ell=\min_{r'\ge r}\beta_{r'}B^{r'}_\ell,\qquad T^0_\ell=0.\qquad(26)$$
--
--   For an edge $e=(i,j)$ with possible positive surplus ($v^{n_i}_i>c^1_j$) and residual reports $\omega$, $r_{e,\omega}(\ell)$ is the number of seller types at which $M^*$ selects $e$ when buyer $i$ reports $v^\ell_i$. For a table $T^r_{e,\ell}$,
--   $$T_\alpha(\mathcal I)=\sum_{e=(i,j)}\mathbb E_\omega\Big[\sum_\ell f_{B_i}(v^\ell_i)\,T^{r_{e,\omega}(\ell)}_{e,\ell}\Big],$$
--   $\beta_e=\min_r\beta_r$ (from $e$'s endpoint priors) and $\mathrm{FB}_e=\mathbb E[(v_i-c_j)\mathbf 1\{e\in M^*\}]$. A table **satisfies Theorem B.11** on $e$ if on the prefix caps it is nonnegative, nondecreasing in $r$, zero at $r=0$, and $F_S(\kappa_r)V_\alpha(F_B,F_S^{\kappa_r})\ge\sum_\ell f_B(v_\ell)T^r_{e,\ell}$ for every $r\ge1$ and every buyer prior with support $\{v^1_i,\dots,v^{n_i}_i\}$.
--
--   These are the objects of the market-level benchmark (Theorem B.14).
--
--   **Formalization Note** Atoms are listed from index $0$ with the published `sortedAtom`; $\beta_r$ is computed in `EReal` with whole-line bilateral $V_\alpha$ and converted to $\mathbb R$ (it lies in $[0,1+\alpha]$ when $v^n>c^1$). Sums run over the edges with possible positive surplus; the other edges are never selected by $M^*$.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490adbe231952acc5fc467ea7dfe37f237d7ce95248cd45c10451aedf4984), App. B.3.2, pp.38–40 (pdf pp.40–42): B^r_ℓ p.38, eq. (25) and (26) p.39, T_α(I), r_{e,ω}(ℓ), β_e, FB_e pp.39–40

import Mathlib
import Definitions.Def_BilatMatch_ValphaOn
import Definitions.Def_BilatMatch_FB
import Definitions.Def_BilatMatch_bilateral
import Definitions.Def_BilatMatch_canonicalMax
import Definitions.Def_BilatMatch_reconLaw
import Definitions.Def_BilatMatch_massLagrangian

open MeasureTheory

namespace BilatMatch.Supplement

open BilatMatch

/-!
# Bilateral targets and the market-level benchmark `T_α(I)` (App. B.3.2)

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), App. B.3.2, pp.38–40 (pdf pp.40–42): `κ_r`,
`B^r_ℓ`, `β_r` (eq. (25)), the targets (26), the prefix lengths `r_{e,ω}(ℓ)`, `T_α(I)`, `β_e`, `FB_e`.

**Formalization Note**
* Finite priors are listed through the published `sortedAtom` / `nAtoms` / `atomMass`
  (`BilatMatch.reconLaw`): buyer `i`'s support is `v^0 < ⋯ < v^{n_i − 1}` (the paper's
  `v^1 < ⋯ < v^{n_i}`, indices shifted to start at `0`), seller `j`'s costs `c_0 < ⋯ < c_{m_j − 1}`.
* `prefixCap F r = {c_0, …, c_{r−1}}` is the paper's `κ_r = {c_1, …, c_r}`; `κ_0 = ∅`. For a finitely
  supported seller these are exactly the caps (initial sets) of its support.
* `betaR α v F r` is eq. (25): the infimum over buyer priors on the support `v` with positive weights
  of `V_α(F_B, F^{κ_r}_S)/FB(F_B, F^{κ_r}_S)`, computed in `EReal` (whole-line bilateral `V_α`, the
  conditional prior `ProbabilityTheory.cond`) and converted to `ℝ`. Under the paper's assumption
  `v^n > c^1` every denominator is positive and the infimum lies in `[0, 1 + α]` (p.39), so the
  conversion loses nothing.
* `posEdges I` are the edges "with possible positive surplus": some buyer atom exceeds some seller
  atom (equivalently `v^{n_i}_i > c^1_j`). Edges outside it are never selected by `M*` (fewest
  edges), so they contribute `0` to `T_α(I)` and to `∑_e β_e FB_e`; the sums run over `posEdges I`.
* Tables `T e r ℓ` are indexed by the edge, the prefix length `r` and the buyer index `ℓ`.
-/

variable {B S : Type*}

/-- `κ_r = {c_1, …, c_r}`: the first `r` atoms of `F` (indices `0, …, r − 1`). -/
noncomputable def prefixCap (F : Measure ℝ) (r : ℕ) : Set ℝ := sortedAtom F '' {k | k < r}

/-- `B^r_ℓ = ∑_{k ≤ r} f_S(c_k)(v_ℓ − c_k)_+` (p.38), unnormalized, for a buyer value `x = v_ℓ`. -/
noncomputable def Bsum (F : Measure ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range r, atomMass F k * max (x - sortedAtom F k) 0

/-- `β_r` (eq. (25), p.39): the infimum over buyer priors `F_B = ∑_ℓ w_ℓ δ_{v_ℓ}` with positive
weights of `V_α(F_B, F^{κ_r}_S)/FB(F_B, F^{κ_r}_S)`. -/
noncomputable def betaR (α : ℝ) {n : ℕ} (v : Fin n → ℝ) (F : Measure ℝ) (r : ℕ) : ℝ :=
  (⨅ (w : Fin n → ℝ) (_ : (∀ ℓ, 0 < w ℓ) ∧ ∑ ℓ, w ℓ = 1),
    Valpha (bilateral (finiteLaw v w) (ProbabilityTheory.cond F (prefixCap F r))) α /
      (((FB (bilateral (finiteLaw v w) (ProbabilityTheory.cond F (prefixCap F r)))).toReal : ℝ) :
        EReal)).toReal

/-- Buyer `i`'s support as a vector `v^0 < ⋯ < v^{n_i − 1}`. -/
noncomputable def buyerSupport (I : Market B S) (i : B) : Fin (nAtoms (I.buyerLaw i)) → ℝ :=
  fun ℓ => sortedAtom (I.buyerLaw i) ℓ

/-- The edges with possible positive surplus: some value atom of the buyer exceeds some cost atom of
the seller. -/
def posEdges (I : Market B S) : Set (B × S) :=
  {e | e ∈ I.edges ∧ ∃ x ∈ atoms (I.buyerLaw e.1), ∃ c ∈ atoms (I.sellerLaw e.2), c < x}

/-- The envelope targets (26) of edge `e`: `T^0_ℓ = 0` and
`T^r_ℓ = min_{r ≤ r' ≤ m} β_{r'} B^{r'}_ℓ` for `r ≥ 1`, from `e`'s endpoint priors. -/
noncomputable def envelopeTable (α : ℝ) (I : Market B S) (e : B × S) (r ℓ : ℕ) : ℝ :=
  if r = 0 then 0 else
    sInf ((fun r' => betaR α (buyerSupport I e.1) (I.sellerLaw e.2) r' *
      Bsum (I.sellerLaw e.2) r' (sortedAtom (I.buyerLaw e.1) ℓ)) ''
        Set.Icc r (nAtoms (I.sellerLaw e.2)))

/-- `β_e = min_{1 ≤ r ≤ m} β_r` from edge `e`'s endpoint priors (p.40). -/
noncomputable def betaE (α : ℝ) (I : Market B S) (e : B × S) : ℝ :=
  sInf ((fun r => betaR α (buyerSupport I e.1) (I.sellerLaw e.2) r) ''
    Set.Icc 1 (nAtoms (I.sellerLaw e.2)))

open Classical in
/-- `r_{e,ω}(ℓ)` (p.39): the number of seller types `c^k_j` at which `M*` selects `e = (i, j)` when
buyer `i` reports `v^ℓ_i` and the others report as in `ω` (its `i`, `j` coordinates are ignored). -/
noncomputable def prefixCount (I : Market B S) (rank : Set (B × S) → ℕ) (e : B × S)
    (ω : Profile B S) (ℓ : ℕ) : ℕ :=
  ((Finset.range (nAtoms (I.sellerLaw e.2))).filter fun k =>
    sortedAtom (I.sellerLaw e.2) k ∈
      firstBestCap I rank e ω (sortedAtom (I.buyerLaw e.1) ℓ)).card

/-- `T_α(I) = ∑_{e=(i,j)} E_ω[∑_ℓ f_{B_i}(v^ℓ_i) T^{r_{e,ω}(ℓ)}_{e,ℓ}]` (p.39) for a table `T`. -/
noncomputable def marketTarget (I : Market B S) (rank : Set (B × S) → ℕ)
    (T : B × S → ℕ → ℕ → ℝ) : ℝ :=
  ∑ᶠ e ∈ posEdges I, ∫ θ, ∑ ℓ ∈ Finset.range (nAtoms (I.buyerLaw e.1)),
    atomMass (I.buyerLaw e.1) ℓ * T e (prefixCount I rank e θ ℓ) ℓ ∂typeMeasure I

open Classical in
/-- `FB_e = E[(v_i − c_j) 1{e ∈ M*}]` (p.40). -/
noncomputable def FBe (I : Market B S) (rank : Set (B × S) → ℕ) (e : B × S) : ℝ :=
  ∫ θ, (if e ∈ firstBestMatching I rank θ then θ.1 e.1 - θ.2 e.2 else 0) ∂typeMeasure I

/-- A table `T e r ℓ` satisfies Theorem B.11 on each edge with possible positive surplus
(p.39): on the prefix caps of the seller support it is nonnegative, nondecreasing in the cap, zero on
the empty cap (the only zero-mass cap), and condition (i) of Theorem B.11 holds: for every
positive-mass cap `κ_r` (`1 ≤ r ≤ m_j`) and every buyer prior on `i`'s support with positive weights,
`F_S(κ_r) V_α(F_B, F^{κ_r}_S) ≥ ∑_ℓ f_B(v_ℓ) T^r_{e,ℓ}`. -/
def IsB11Table (α : ℝ) (I : Market B S) (T : B × S → ℕ → ℕ → ℝ) : Prop :=
  ∀ e ∈ posEdges I,
    (∀ r ≤ nAtoms (I.sellerLaw e.2), ∀ ℓ < nAtoms (I.buyerLaw e.1), 0 ≤ T e r ℓ) ∧
    (∀ r < nAtoms (I.sellerLaw e.2), ∀ ℓ < nAtoms (I.buyerLaw e.1), T e r ℓ ≤ T e (r + 1) ℓ) ∧
    (∀ ℓ < nAtoms (I.buyerLaw e.1), T e 0 ℓ = 0) ∧
    ∀ r, 1 ≤ r → r ≤ nAtoms (I.sellerLaw e.2) →
      ∀ w : Fin (nAtoms (I.buyerLaw e.1)) → ℝ, (∀ ℓ, 0 < w ℓ) → ∑ ℓ, w ℓ = 1 →
        ((∑ ℓ, w ℓ * T e r ℓ : ℝ) : EReal) ≤
          (((I.sellerLaw e.2) (prefixCap (I.sellerLaw e.2) r)).toReal : EReal) *
            Valpha (bilateral (finiteLaw (buyerSupport I e.1) w)
              (ProbabilityTheory.cond (I.sellerLaw e.2) (prefixCap (I.sellerLaw e.2) r))) α

end BilatMatch.Supplement


