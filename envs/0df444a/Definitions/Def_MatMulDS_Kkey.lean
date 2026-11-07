-- Prove2me | Definitions.Def_MatMulDS_Kkey
-- name    : MatMulDS_Kkey
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:04:40.144412+00:00
-- url     : https://prove2.me/theorems/78bed210-631f-4512-85e5-aa8053c26a4a
-- title:
--   Selected outputs, light products, boxes and keys
-- statement:
--   An output $o=o_1\cdots o_{2L}$ of $T_{\mathrm{big}}$ is **selected** if each block $\beta$ contains exactly $L\pi(\beta)$ of $o_1,\dots,o_L$ and exactly $L\pi(\beta)$ of $o_{L+1},\dots,o_{2L}$. A string $p=p_1\cdots p_{2L}$ of products is **light** if its average weight is at most $\eta_{\mathrm{pre}}$, and **relevant** to $o$ if each $p_\ell$ is relevant to $o_\ell$. Its order is $\mathrm{ord}_o(p)=\sum_\ell(\mathrm{wt}(\rho(o_\ell))-\mathrm{wt}(p_\ell))$, and $t=2L(\mu-\eta_{\mathrm{pre}})$.
--
--   A **box** $(\ast o_1,\dots,\ast o_k,p_{k+1},\dots,p_{2L})$ is the set of strings relevant to $o_\ell$ for $\ell\le k$ and equal to $p_\ell$ for $\ell>k$. Its key is $(\kappa,k)$, where $\kappa$ replaces each $\ast o_\ell$ by $\rho(o_\ell)$, and
--   $$K_{\mathrm{key}}=\{(\kappa,k):\kappa\text{ light},\ 0\le k\le 2L,\ \kappa_\ell\in\rho(O)\text{ for }\ell\le k\}.$$
--   For a light string $p$ relevant to $o$, the box $b_o(p)$ keeps the shortest suffix of $p$ whose order reaches $t$. These objects define which products are precomputed and how a query is answered.
--
--   **Formalization Note** Positions are 0-based here, so the symbols $\ast$ are at positions $\ell<k$. Lightness is written without division, $\sum_\ell\mathrm{wt}(p_\ell)\le2L\eta_{\mathrm{pre}}$, which is the same for $L\ge1$.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), §5.4, pp.28–30 (PDF pp.30–32); §A.2–A.3, pp.68–75 (PDF pp.70–77)

import Mathlib
import Definitions.Def_MatMulDS_IdentityData

set_option autoImplicit false

namespace MatMulDS

variable {I K J B P : Type} [Fintype I] [Fintype K] [Fintype J] [Fintype B] [Fintype P]
  [DecidableEq I] [DecidableEq K] [DecidableEq J] [DecidableEq B] [DecidableEq P]

/-- A string `p = p1 ⋯ p2L` of products of the base identity (§5.4, p.28). -/
abbrev Str (P : Type) (L : ℕ) : Type := Fin (2 * L) → P

variable {T : BlockTensor I K J B}

/-- An output `o = o1 ⋯ o2L` of `T_big` is **selected** (p.29; p.68): for every block `β`, exactly `Lπ(β)` of
`o1, …, oL` lie in `β`, and likewise exactly `Lπ(β)` of `o_{L+1}, …, o_{2L}`. -/
def IsSelected (π : I × J → ℚ) (L : ℕ) (o : Fin (2 * L) → T.Out) : Prop :=
  ∀ β,
    (((Finset.univ.filter fun ℓ : Fin (2 * L) =>
        (ℓ : ℕ) < L ∧ (o ℓ).1 ∈ T.blockOutputs β).card : ℕ) : ℚ) = L * piBlock T π β ∧
    (((Finset.univ.filter fun ℓ : Fin (2 * L) =>
        L ≤ (ℓ : ℕ) ∧ (o ℓ).1 ∈ T.blockOutputs β).card : ℕ) : ℚ) = L * piBlock T π β

/-- A string is **light** (p.30; p.74): its average weight `(1/2L) Σ_ℓ wt(p_ℓ)` is at most `η_pre`.

**Formalization Note** Written without the division; the two agree for `L ≥ 1`, and all statements take `L`
large. -/
def IsLight {L : ℕ} (wt : P → ℝ) (η : ℝ) (p : Str P L) : Prop :=
  ∑ ℓ, wt (p ℓ) ≤ 2 * (L : ℝ) * η

/-- A product `p` is **relevant** to `o` (p.28): `p_ℓ ∈ Prel(o_ℓ)` for every `ℓ`. -/
def IsRelevant (D : IdentityData I K J P) {L : ℕ} (o : Fin (2 * L) → T.Out) (p : Str P L) : Prop :=
  ∀ ℓ, p ℓ ∈ D.Prel (o ℓ).1

/-- The set of products relevant to `o`. -/
noncomputable def relevantSet (D : IdentityData I K J P) {L : ℕ} (o : Fin (2 * L) → T.Out) :
    Finset (Str P L) :=
  open Classical in Finset.univ.filter (IsRelevant D o)

/-- `a_ℓ = wt(ρ(o_ℓ)) − wt(p_ℓ)`, (A.16), p.74. -/
def aCoord (ρ : T.Out → P) (wt : P → ℝ) {L : ℕ} (o : Fin (2 * L) → T.Out) (p : Str P L)
    (ℓ : Fin (2 * L)) : ℝ :=
  wt (ρ (o ℓ)) - wt (p ℓ)

/-- The order `ord_o(p) = Σ_ℓ a_ℓ`, (A.16), p.74. -/
def ordOf (ρ : T.Out → P) (wt : P → ℝ) {L : ℕ} (o : Fin (2 * L) → T.Out) (p : Str P L) : ℝ :=
  ∑ ℓ, aCoord ρ wt o p ℓ

/-- The threshold `t = 2L(µ − η_pre)`, p.74. -/
noncomputable def threshold (π : I × J → ℚ) (ρ : T.Out → P) (wt : P → ℝ) (η : ℝ) (L : ℕ) : ℝ :=
  2 * (L : ℝ) * (mu π ρ wt - η)

/-- The set named by the key `(κ, k)` (p.75): the strings whose `ℓ`th coordinate is relevant to the output with
private product `κ_ℓ`, for the first `k` coordinates, and equals `κ_ℓ` for the others.

**Formalization Note** Coordinates are 0-based, so the symbols `∗` are at `ℓ < k`, and `k` runs over `0, …, 2L`, as
on p.75. -/
noncomputable def keyBox (D : IdentityData I K J P) (ρ : T.Out → P) {L : ℕ} (κ : Str P L) (k : ℕ) :
    Finset (Str P L) :=
  open Classical in
  Finset.univ.filter fun p => ∀ ℓ : Fin (2 * L),
    ((ℓ : ℕ) < k → ∃ o' : T.Out, ρ o' = κ ℓ ∧ p ℓ ∈ D.Prel o'.1) ∧ (k ≤ (ℓ : ℕ) → p ℓ = κ ℓ)

/-- The set `Kkey = {(κ, k) : κ ∈ P^{2L} is light, 0 ≤ k ≤ 2L, and κ_ℓ ∈ ρ(O) for all ℓ ≤ k}`, p.75. -/
noncomputable def Kkey (ρ : T.Out → P) (wt : P → ℝ) (η : ℝ) (L : ℕ) : Finset (Str P L × ℕ) :=
  open Classical in
  ((Finset.univ : Finset (Str P L)) ×ˢ Finset.range (2 * L + 1)).filter fun x =>
    IsLight wt η x.1 ∧ ∀ ℓ : Fin (2 * L), (ℓ : ℕ) < x.2 → ∃ o' : T.Out, ρ o' = x.1 ℓ

/-- The index of p.75 for a light product `p` relevant to a selected output `o`, 0-based: the largest
`k ∈ {0, …, 2L}` such that the suffix sum `Σ_{ℓ≥k} a_ℓ` is at least `t`. -/
noncomputable def suffixIndex (π : I × J → ℚ) (ρ : T.Out → P) (wt : P → ℝ) (η : ℝ) {L : ℕ}
    (o : Fin (2 * L) → T.Out) (p : Str P L) : ℕ :=
  open Classical in
  Nat.findGreatest
    (fun k => threshold π ρ wt η L ≤
      ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin (2 * L) => k ≤ (ℓ : ℕ)), aCoord ρ wt o p ℓ) (2 * L)

/-- The string of the key of `b_o(p)` (p.75): the private products of `o` before the index, then `p`. -/
noncomputable def keyOf (π : I × J → ℚ) (ρ : T.Out → P) (wt : P → ℝ) (η : ℝ) {L : ℕ}
    (o : Fin (2 * L) → T.Out) (p : Str P L) : Str P L :=
  fun ℓ => if (ℓ : ℕ) < suffixIndex π ρ wt η o p then ρ (o ℓ) else p ℓ

/-- The box `b_o(p) = (∗o_1, …, ∗o_{j−1}, p_j, …, p_2L)` of p.75: replace the prefix of `p` by the symbols `∗` for
the corresponding outputs of `o`. -/
noncomputable def boxOf (D : IdentityData I K J P) (π : I × J → ℚ) (ρ : T.Out → P) (wt : P → ℝ)
    (η : ℝ) {L : ℕ} (o : Fin (2 * L) → T.Out) (p : Str P L) : Finset (Str P L) :=
  open Classical in
  Finset.univ.filter fun p' => ∀ ℓ : Fin (2 * L),
    ((ℓ : ℕ) < suffixIndex π ρ wt η o p → p' ℓ ∈ D.Prel (o ℓ).1) ∧
    (suffixIndex π ρ wt η o p ≤ (ℓ : ℕ) → p' ℓ = p ℓ)

/-- The light products relevant to `o`. -/
noncomputable def lightRelevant (D : IdentityData I K J P) (wt : P → ℝ) (η : ℝ) {L : ℕ}
    (o : Fin (2 * L) → T.Out) : Finset (Str P L) :=
  open Classical in (relevantSet D o).filter (IsLight wt η)

/-- The set `B_o` of all boxes `b_o(p)`, p.75. -/
noncomputable def boxesOf (D : IdentityData I K J P) (π : I × J → ℚ) (ρ : T.Out → P) (wt : P → ℝ)
    (η : ℝ) {L : ℕ} (o : Fin (2 * L) → T.Out) : Finset (Finset (Str P L)) :=
  open Classical in (lightRelevant D wt η o).image (boxOf D π ρ wt η o)

/-- The products relevant to `o` of order less than `t`: the first sum of (A.17), p.75. -/
noncomputable def heavyRelevant (π : I × J → ℚ) (D : IdentityData I K J P) (ρ : T.Out → P)
    (wt : P → ℝ) (η : ℝ) {L : ℕ} (o : Fin (2 * L) → T.Out) : Finset (Str P L) :=
  open Classical in (relevantSet D o).filter fun p => ordOf ρ wt o p < threshold π ρ wt η L

end MatMulDS


