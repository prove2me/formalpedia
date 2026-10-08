-- Prove2me | Definitions.Def_SantosHirsch_Counter_Setting
-- name    : SantosHirsch_Counter_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:31:04.752579+00:00
-- url     : https://prove2.me/theorems/0ebb9b4e-5708-4cec-9dfa-5193a0beace5
-- title:
--   Def. 1.4, Table 1, Table 2 — facet presentations, spindles, Santos's 48 points and the 322 polar vertices
-- statement:
--   This file fixes the vocabulary of the mission on top of the platform model `Hirsch_model` / `Hirsch_walk`, where $\mathrm{Hpoly}(a,b)=\{x\in\mathbb R^d:\langle a_i,x\rangle\le b_i\ \forall i\}$ for $a_1,\dots,a_n\in\mathbb R^d$ and $b\in\mathbb R^n$.
--
--   1. **Facet presentation.** The pair $(a,b)$ is a *facet presentation* if $\mathrm{Hpoly}(a,b)$ has nonempty interior and every inequality is irredundant: for each $i$ there is a point satisfying all inequalities $j\neq i$ and violating inequality $i$. For a bounded $\mathrm{Hpoly}(a,b)$ this says that it is a $d$-polytope and that its $n$ inequalities are in bijection with its facets, so $n$ is the number of facets.
--   2. **Non-Hirsch.** $(a,b)$ is *non-Hirsch* if the combinatorial diameter of $\mathrm{Hpoly}(a,b)$ is not at most $n-d$ (Santos, p. 1: a polytope is non-Hirsch if it violates the bound $n-d$ of the Hirsch conjecture).
--   3. **Spindle** (Definition 1.4). Distinct vertices $u,v$ of $\mathrm{Hpoly}(a,b)$ make it a *spindle* if every inequality is tight at exactly one of $u$ and $v$: $\langle a_i,u\rangle=b_i \iff \langle a_i,v\rangle\neq b_i$.
--   4. **Table 1** (p. 11). The 48 vectors $1^+,\dots,24^+,1^-,\dots,24^-\in\mathbb R^5$, listed entry by entry as on the page; the first 24 have $x_5=1$, the last 24 have $x_5=-1$. They are the vertices of Santos's prismatoid $Q$.
--   5. **The polar spindle** $Q^\Delta=\{x\in\mathbb R^5:\langle r,x\rangle\le 1\text{ for each row } r \text{ of Table 1}\}$, and the apices $e_5=(0,0,0,0,1)$ and $-e_5$, the polar points of the base facets $Q^+\subset\{x_5=1\}$ (row A of Table 2) and $Q^-\subset\{x_5=-1\}$ (row L).
--   6. **Table 2** (p. 12). For each letter $X\in\{B,\dots,K\}$, primed or not, the coefficients $(c_1,c_2,c_3,c_4)$ of $x_1,\dots,x_4$, the coefficient $c_5$ of $x_5$ and the right-hand side $c_0$ of the facet inequalities $\pm c_1x_1\pm c_2x_2\pm c_3x_3\pm c_4x_4+c_5x_5\le c_0$. The polar point of a facet with sign pattern $\sigma\in\{\pm1\}^4$ is
--   $$\tfrac1{c_0}\,(\sigma_1c_1,\sigma_2c_2,\sigma_3c_3,\sigma_4c_4,c_5).$$
--   The set of the 322 polar points consists of $\pm e_5$ and these $20\times16$ points; the 32 points of a letter (types $X$ and $X'$) form its *letter class*.
--   7. **Symmetries** (p. 11). The 32 orthogonal maps generating $\Sigma^+$ (sign changes of $x_1,\dots,x_4$, optionally composed with the simultaneous transpositions $x_1\leftrightarrow x_2$, $x_3\leftrightarrow x_4$), the map $(x_1,\dots,x_5)\mapsto(x_4,x_3,x_1,x_2,-x_5)$, the $\Sigma^+$- and $\Sigma$-orbits of a point, and the pairing $B\leftrightarrow K$, $C\leftrightarrow J$, $D\leftrightarrow I$, $E\leftrightarrow H$, $F\leftrightarrow G$ of Theorem 4.1.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Santos works with the prismatoid $Q$ and its dual graph; Mathlib has no polarity of polytopes, so the mission works in the polar, as the paper itself licenses (p. 6: "Q is dual-Hirsch if and only if its polar polytope is Hirsch"; p. 8: prismatoids are "the polars of the spindles"). Since $0\in\operatorname{int}Q$, the vertices of $Q$ become the rows $\langle r,x\rangle\le1$ of $Q^\Delta$ and the facets of $Q$ become the vertices of $Q^\Delta$. Table 2's inequalities are stored by the coefficient of each coordinate $x_1,\dots,x_4$ in order, so the primed types, which the page writes with permuted coordinates, read differently from the page's column order.
-- source:
--   Santos, A counterexample to the Hirsch conjecture, arXiv:1006.2814v3, pp. 1, 4, 11, 12, Definition 1.4, Table 1, Table 2, §3 (symmetries)

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk

open scoped RealInnerProductSpace

namespace SantosHirsch.Counter

noncomputable section

/-- `IsFacetPresentation a b`: the H-polytope `{x | ∀ i, ⟪a i, x⟫ ≤ b i}` in `ℝ^d` is
full-dimensional (nonempty interior) and every one of its `n` inequalities is irredundant
(dropping row `i` admits a point violating it). Together with boundedness this says the
polytope is a `d`-polytope whose `n` rows are in bijection with its facets. -/
def IsFacetPresentation {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Prop :=
  (interior (Hirsch.Hpoly a b)).Nonempty ∧
    ∀ i, ∃ x, (∀ j, j ≠ i → ⟪a j, x⟫ ≤ b j) ∧ b i < ⟪a i, x⟫

/-- `IsNonHirsch a b`: the polytope `Hpoly a b` (a `d`-polytope with `n` facets when `a, b`
is a bounded facet presentation) has combinatorial diameter greater than `n - d`. -/
def IsNonHirsch {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) : Prop :=
  ¬ Hirsch.DiamLE (Hirsch.Hpoly a b) (n - d)

/-- `IsSpindle a b u v` (Definition 1.4): `u` and `v` are distinct vertices of
`Hpoly a b` and every row (facet) is tight at exactly one of them. -/
def IsSpindle {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) : Prop :=
  u ≠ v ∧
    u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) ∧
    v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) ∧
    ∀ i, (⟪a i, u⟫ = b i ↔ ⟪a i, v⟫ ≠ b i)

/-- Table 1 of Santos (p. 11), row by row: entries `0 … 23` are the vertices `1⁺ … 24⁺`,
entries `24 … 47` are the vertices `1⁻ … 24⁻`, each as `(x₁, x₂, x₃, x₄, x₅)`. -/
def santosMatrix : Fin 48 → Fin 5 → ℝ :=
  ![![18, 0, 0, 0, 1],      -- 1⁺
    ![-18, 0, 0, 0, 1],     -- 2⁺
    ![0, 18, 0, 0, 1],      -- 3⁺
    ![0, -18, 0, 0, 1],     -- 4⁺
    ![0, 0, 45, 0, 1],      -- 5⁺
    ![0, 0, -45, 0, 1],     -- 6⁺
    ![0, 0, 0, 45, 1],      -- 7⁺
    ![0, 0, 0, -45, 1],     -- 8⁺
    ![15, 15, 0, 0, 1],     -- 9⁺
    ![-15, 15, 0, 0, 1],    -- 10⁺
    ![15, -15, 0, 0, 1],    -- 11⁺
    ![-15, -15, 0, 0, 1],   -- 12⁺
    ![0, 0, 30, 30, 1],     -- 13⁺
    ![0, 0, -30, 30, 1],    -- 14⁺
    ![0, 0, 30, -30, 1],    -- 15⁺
    ![0, 0, -30, -30, 1],   -- 16⁺
    ![0, 10, 40, 0, 1],     -- 17⁺
    ![0, -10, 40, 0, 1],    -- 18⁺
    ![0, 10, -40, 0, 1],    -- 19⁺
    ![0, -10, -40, 0, 1],   -- 20⁺
    ![10, 0, 0, 40, 1],     -- 21⁺
    ![-10, 0, 0, 40, 1],    -- 22⁺
    ![10, 0, 0, -40, 1],    -- 23⁺
    ![-10, 0, 0, -40, 1],   -- 24⁺
    ![0, 0, 0, 18, -1],     -- 1⁻
    ![0, 0, 0, -18, -1],    -- 2⁻
    ![0, 0, 18, 0, -1],     -- 3⁻
    ![0, 0, -18, 0, -1],    -- 4⁻
    ![45, 0, 0, 0, -1],     -- 5⁻
    ![-45, 0, 0, 0, -1],    -- 6⁻
    ![0, 45, 0, 0, -1],     -- 7⁻
    ![0, -45, 0, 0, -1],    -- 8⁻
    ![0, 0, 15, 15, -1],    -- 9⁻
    ![0, 0, 15, -15, -1],   -- 10⁻
    ![0, 0, -15, 15, -1],   -- 11⁻
    ![0, 0, -15, -15, -1],  -- 12⁻
    ![30, 30, 0, 0, -1],    -- 13⁻
    ![-30, 30, 0, 0, -1],   -- 14⁻
    ![30, -30, 0, 0, -1],   -- 15⁻
    ![-30, -30, 0, 0, -1],  -- 16⁻
    ![40, 0, 10, 0, -1],    -- 17⁻
    ![40, 0, -10, 0, -1],   -- 18⁻
    ![-40, 0, 10, 0, -1],   -- 19⁻
    ![-40, 0, -10, 0, -1],  -- 20⁻
    ![0, 40, 0, 10, -1],    -- 21⁻
    ![0, 40, 0, -10, -1],   -- 22⁻
    ![0, -40, 0, 10, -1],   -- 23⁻
    ![0, -40, 0, -10, -1]]  -- 24⁻

/-- The 48 rows of Table 1 as vectors of `ℝ⁵`; they are the vertices of Santos's
prismatoid `Q` and, in the polar, the normals of the 48 facets of the spindle. -/
def santosRows (i : Fin 48) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 (santosMatrix i)

/-- The polar of Santos's prismatoid: `{x ∈ ℝ⁵ | ⟪r, x⟫ ≤ 1 for every row r of Table 1}`. -/
def santosSpindle : Set (EuclideanSpace ℝ (Fin 5)) :=
  Hirsch.Hpoly santosRows (fun _ => 1)

/-- `e₅ = (0, 0, 0, 0, 1)`, the polar of the base facet `Q⁺ ⊂ {x₅ = 1}` (row A of Table 2). -/
def apexPlus : EuclideanSpace ℝ (Fin 5) := EuclideanSpace.single (4 : Fin 5) 1

/-- `−e₅ = (0, 0, 0, 0, −1)`, the polar of the base facet `Q⁻ ⊂ {x₅ = −1}` (row L of Table 2). -/
def apexMinus : EuclideanSpace ℝ (Fin 5) := EuclideanSpace.single (4 : Fin 5) (-1)

/-- The ten letters `B, …, K` of Table 2 (the rows A and L are the two apices). -/
inductive Letter
  | B | C | D | E | F | G | H | I | J | K
  deriving DecidableEq

/-- Table 2 (p. 12): for a letter and `primed = false` (the type `X`) or `primed = true`
(the type `X′`), the coefficients `(c₁, c₂, c₃, c₄)` of the coordinates `x₁, x₂, x₃, x₄`
in the facet inequality `c₀ − c₅ x₅ ≥ ±c₁ x₁ ± c₂ x₂ ± c₃ x₃ ± c₄ x₄`. -/
def typeCoeffs : Letter → Bool → Fin 4 → ℝ
  | .B, false => ![5, 1, 2, 1]
  | .B, true  => ![1, 5, 1, 2]
  | .C, false => ![4, 2, 7 / 4, 5 / 4]
  | .C, true  => ![2, 4, 5 / 4, 7 / 4]
  | .D, false => ![4, 1, 2, 1]
  | .D, true  => ![1, 4, 1, 2]
  | .E, false => ![3, 3 / 2, 3 / 2, 1]
  | .E, true  => ![3 / 2, 3, 1, 3 / 2]
  | .F, false => ![2, 1, 1, 1]
  | .F, true  => ![1, 2, 1, 1]
  | .G, false => ![1, 1, 1, 2]
  | .G, true  => ![1, 1, 2, 1]
  | .H, false => ![3 / 2, 1, 3 / 2, 3]
  | .H, true  => ![1, 3 / 2, 3, 3 / 2]
  | .I, false => ![2, 1, 1, 4]
  | .I, true  => ![1, 2, 4, 1]
  | .J, false => ![7 / 4, 5 / 4, 2, 4]
  | .J, true  => ![5 / 4, 7 / 4, 4, 2]
  | .K, false => ![2, 1, 1, 5]
  | .K, true  => ![1, 2, 5, 1]

/-- Table 2: the coefficient `c₅` of `x₅` once the inequality is written as
`±c₁x₁ ± c₂x₂ ± c₃x₃ ± c₄x₄ + c₅x₅ ≤ c₀` (so `c₅ = 135/2` for B, `−15` for G). It is the
same for `X` and `X′`. -/
def typeC5 : Letter → ℝ
  | .B => 135 / 2
  | .C => 45
  | .D => 45
  | .E => 30
  | .F => 15
  | .G => -15
  | .H => -30
  | .I => -45
  | .J => -45
  | .K => -135 / 2

/-- Table 2: the constant term `c₀` (the right-hand side). -/
def typeRhs : Letter → ℝ
  | .B => 315 / 2
  | .C => 135
  | .D => 135
  | .E => 105
  | .F => 75
  | .G => 75
  | .H => 105
  | .I => 135
  | .J => 135
  | .K => 315 / 2

/-- The sign `+1` (`true`) or `−1` (`false`). -/
def sgn (s : Bool) : ℝ := if s then 1 else -1

/-- The polar point of the facet of type `(ℓ, primed)` with sign pattern `σ`:
`(1 / c₀) • (σ₁c₁, σ₂c₂, σ₃c₃, σ₄c₄, c₅)`, so that the facet inequality reads
`⟪facetPoint ℓ primed σ, x⟫ ≤ 1`. -/
def facetPoint (ℓ : Letter) (primed : Bool) (σ : Fin 4 → Bool) :
    EuclideanSpace ℝ (Fin 5) :=
  (1 / typeRhs ℓ) • WithLp.toLp 2
    ![sgn (σ 0) * typeCoeffs ℓ primed 0, sgn (σ 1) * typeCoeffs ℓ primed 1,
      sgn (σ 2) * typeCoeffs ℓ primed 2, sgn (σ 3) * typeCoeffs ℓ primed 3, typeC5 ℓ]

/-- The 32 polar points carrying the letter `ℓ` (types `ℓ` and `ℓ′`, 16 sign patterns each). -/
def letterPoints (ℓ : Letter) : Set (EuclideanSpace ℝ (Fin 5)) :=
  Set.range (fun p : Bool × (Fin 4 → Bool) => facetPoint ℓ p.1 p.2)

/-- The 322 polar points of Table 2: `e₅` (row A), `−e₅` (row L) and the `20 × 16` points
of the types `B, B′, …, K, K′`. -/
def santosVertices : Set (EuclideanSpace ℝ (Fin 5)) :=
  {apexPlus, apexMinus} ∪ ⋃ ℓ : Letter, letterPoints ℓ

/-- The 32 orthogonal maps of p. 11 generating `Σ⁺`: sign changes of `x₁, …, x₄`
(`swap = false`, the diagonal matrices), optionally composed with the simultaneous
transpositions `x₁ ↔ x₂`, `x₃ ↔ x₄` (`swap = true`, the second matrix). -/
def sigmaPlusMap (s : Fin 4 → Bool) (swap : Bool) (x : EuclideanSpace ℝ (Fin 5)) :
    EuclideanSpace ℝ (Fin 5) :=
  if swap then
    WithLp.toLp 2 ![sgn (s 0) * x 1, sgn (s 1) * x 0, sgn (s 2) * x 3, sgn (s 3) * x 2, x 4]
  else
    WithLp.toLp 2 ![sgn (s 0) * x 0, sgn (s 1) * x 1, sgn (s 2) * x 2, sgn (s 3) * x 3, x 4]

/-- The orthogonal map `(x₁, x₂, x₃, x₄, x₅) ↦ (x₄, x₃, x₁, x₂, −x₅)` of p. 11, which
exchanges `Q⁺` and `Q⁻`. -/
def sigmaSwap (x : EuclideanSpace ℝ (Fin 5)) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 ![x 3, x 2, x 0, x 1, -x 4]

/-- The `Σ⁺`-orbit of `p`: its images under the 32 maps `sigmaPlusMap`. -/
def sigmaPlusOrbit (p : EuclideanSpace ℝ (Fin 5)) : Set (EuclideanSpace ℝ (Fin 5)) :=
  Set.range (fun g : (Fin 4 → Bool) × Bool => sigmaPlusMap g.1 g.2 p)

/-- The `Σ`-orbit of `p`, for `Σ = Σ⁺ ∪ sigmaSwap ∘ Σ⁺` (64 maps). -/
def sigmaOrbit (p : EuclideanSpace ℝ (Fin 5)) : Set (EuclideanSpace ℝ (Fin 5)) :=
  sigmaPlusOrbit p ∪ sigmaSwap '' sigmaPlusOrbit p

/-- The pairing of letters into `Σ`-orbits stated in Theorem 4.1: `B ∪ K`, `C ∪ J`,
`D ∪ I`, `E ∪ H`, `F ∪ G`. -/
def pairedLetter : Letter → Letter
  | .B => .K
  | .C => .J
  | .D => .I
  | .E => .H
  | .F => .G
  | .G => .F
  | .H => .E
  | .I => .D
  | .J => .C
  | .K => .B

end

end SantosHirsch.Counter


