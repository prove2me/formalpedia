-- Prove2me | Definitions.Def_RPLib_F2_019
-- name    : RPLib_F2_019
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T10:08:17.313281+00:00
-- url     : https://prove2.me/theorems/c73bd7eb-8011-40f7-ad14-d4779614d3e4
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 019 of 70
-- statement:
--   File 019 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_IntersectC_Dense`: S4-IntersectC, file Dense: translates of a separating divisor are dense (L36, O7)
--   * `S4.Def_RP_IntersectC_Pos`: S4-IntersectC, file Pos: positivity of the self-intersection (L36, O9)
--   * `S4.Def_RP_ThetaSquare_CPullOpen`: S4-ThetaSquare, file CPullOpen: `cpull` along open immersions, and monotonicity (F4)
--   * `S4.Def_RP_ThetaSquare_ThetaX0`: Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`
--   * `S4.Def_RP_ThetaSquare_Curve2`: Unit S4-ThetaSquare, file Curve2: the support of `D_e` on `K`-points (T4c, part 2; Riemann-Roch only)
--   * `S4.Def_RP_ThetaSquare_Curve3`: Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)
--   * `S4.Def_RP_ThetaSquare_Curve4`: Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))
--   * `S4.Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
--   * `S4.Def_RP_ThetaSquare_Curve8`: Unit S4-ThetaSquare, file Curve8: points of `X1^g` (T4c (D), nonemptiness, part 1)
--   * `S4.Def_RP_ThetaCube_Proj`: S4-ThetaCube, T7: the projection formula and positivity for pulled-back divisors (L42 inputs)
--   * `S4.Def_RP_IsogDegB_Frob`: S4-IsogDegB, Frobenius-type endomorphisms (lemma L28 of S4_COREB_ROUTE.md §3)
--   * `S4.Def_RP_ThetaCube_Zero`: S4-ThetaCube, T8z: the input `hzero` of DegPoly for the theta divisor
--   * `S4.Def_RP_ThetaCube_Alg`: Unit S4-ThetaCube, file Alg: pure algebra for numerical classes (obligation T6, algebra part)
--   * `S4.Def_RP_ThetaCube_Cube`: S4-ThetaCube, file Cube (T5a): numerical triviality of pulled-back principal multiples
--   * `S4.Def_RP_ThetaCube_Line`: S4-ThetaCube, file Line (D-A, part LT1): the curve test for Weil divisors
--   * `S4.Def_RP_ThetaCube_Cover`: S4-ThetaCube, file Cover (D-A, rest): the line test on `X1^n`
--   * `S4.Def_RP_ThetaCube_CubeZ`: S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`
--   * `S4.Def_RP_ThetaCube_SmPP`: S4-ThetaCube, file SmPP (D-B0, part 2): `X1` and `X1^n` are smooth, so their stalks are factorial
--   * `S4.Def_RP_ThetaCube_FF`: S4-ThetaCube, file FF (D-B1, part 1): the function field of `X1` is `F`
--   * `S4.Def_RP_ThetaCube_Ord`: S4-ThetaCube, file Ord (D-B1, part 2): orders of vanishing on `X1` are the place orders
--   * `S4.Def_RP_ThetaCube_Slice`: S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
--   * `S4.Def_RP_ThetaCube_Rank`: S4-ThetaCube, file Rank (D-B4, part 1): the slices do not vanish
--   * `S4.Def_RP_ThetaCube_Good`: S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
--   * `S4.Def_RP_ThetaCube_Val`: S4-ThetaCube, file Val (D-C1, part 1): values of rational functions at `K`-points
--   * `S4.Def_RP_ThetaCube_Tr`: S4-ThetaCube, file Tr (D-C1, part 2): trace functions on `J` and their values on the chart
--   * `S4.Def_RP_ThetaCube_Cst`: S4-ThetaCube, file Cst (D-C1, part 3): constants and values of `phiX f` at `K`-points
--   * `S4.Def_RP_ThetaCube_TrPP`: S4-ThetaCube, file TrPP (D-C1, part 4): the block trace identity on `X1^n`
--   * `S4.Def_RP_ThetaCube_Bas`: S4-ThetaCube, file Bas (D-C3, part 2): the blocks and the bases of `L(H_S)`
--   * `S4.Def_RP_ThetaCube_TrOpen`: S4-ThetaCube, file TrOpen (D-C1, part 5): the open where the block trace identity is checked
--   * `S4.Def_RP_ThetaCube_TrNe`: S4-ThetaCube, file TrNe (D-C1, part 6): the open `ψ_S⁻¹ VJ` is nonempty
--   * `S4.Def_RP_ThetaCube_GrA`: S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
--   * `S4.Def_RP_DegPoly_Cube`: Degree polynomiality, part 3: the quadratic relation from the cube relation (unit S4-DegPoly)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_018

/-!
# Ramanujan-Petersson curve library (flat edition), file 019 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_IntersectC_Dense`: S4-IntersectC, file Dense: translates of a separating divisor are dense (L36, O7)
* `S4.Def_RP_IntersectC_Pos`: S4-IntersectC, file Pos: positivity of the self-intersection (L36, O9)
* `S4.Def_RP_ThetaSquare_CPullOpen`: S4-ThetaSquare, file CPullOpen: `cpull` along open immersions, and monotonicity (F4)
* `S4.Def_RP_ThetaSquare_ThetaX0`: Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`
* `S4.Def_RP_ThetaSquare_Curve2`: Unit S4-ThetaSquare, file Curve2: the support of `D_e` on `K`-points (T4c, part 2; Riemann-Roch only)
* `S4.Def_RP_ThetaSquare_Curve3`: Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)
* `S4.Def_RP_ThetaSquare_Curve4`: Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))
* `S4.Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
* `S4.Def_RP_ThetaSquare_Curve8`: Unit S4-ThetaSquare, file Curve8: points of `X1^g` (T4c (D), nonemptiness, part 1)
* `S4.Def_RP_ThetaCube_Proj`: S4-ThetaCube, T7: the projection formula and positivity for pulled-back divisors (L42 inputs)
* `S4.Def_RP_IsogDegB_Frob`: S4-IsogDegB, Frobenius-type endomorphisms (lemma L28 of S4_COREB_ROUTE.md §3)
* `S4.Def_RP_ThetaCube_Zero`: S4-ThetaCube, T8z: the input `hzero` of DegPoly for the theta divisor
* `S4.Def_RP_ThetaCube_Alg`: Unit S4-ThetaCube, file Alg: pure algebra for numerical classes (obligation T6, algebra part)
* `S4.Def_RP_ThetaCube_Cube`: S4-ThetaCube, file Cube (T5a): numerical triviality of pulled-back principal multiples
* `S4.Def_RP_ThetaCube_Line`: S4-ThetaCube, file Line (D-A, part LT1): the curve test for Weil divisors
* `S4.Def_RP_ThetaCube_Cover`: S4-ThetaCube, file Cover (D-A, rest): the line test on `X1^n`
* `S4.Def_RP_ThetaCube_CubeZ`: S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`
* `S4.Def_RP_ThetaCube_SmPP`: S4-ThetaCube, file SmPP (D-B0, part 2): `X1` and `X1^n` are smooth, so their stalks are factorial
* `S4.Def_RP_ThetaCube_FF`: S4-ThetaCube, file FF (D-B1, part 1): the function field of `X1` is `F`
* `S4.Def_RP_ThetaCube_Ord`: S4-ThetaCube, file Ord (D-B1, part 2): orders of vanishing on `X1` are the place orders
* `S4.Def_RP_ThetaCube_Slice`: S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
* `S4.Def_RP_ThetaCube_Rank`: S4-ThetaCube, file Rank (D-B4, part 1): the slices do not vanish
* `S4.Def_RP_ThetaCube_Good`: S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
* `S4.Def_RP_ThetaCube_Val`: S4-ThetaCube, file Val (D-C1, part 1): values of rational functions at `K`-points
* `S4.Def_RP_ThetaCube_Tr`: S4-ThetaCube, file Tr (D-C1, part 2): trace functions on `J` and their values on the chart
* `S4.Def_RP_ThetaCube_Cst`: S4-ThetaCube, file Cst (D-C1, part 3): constants and values of `phiX f` at `K`-points
* `S4.Def_RP_ThetaCube_TrPP`: S4-ThetaCube, file TrPP (D-C1, part 4): the block trace identity on `X1^n`
* `S4.Def_RP_ThetaCube_Bas`: S4-ThetaCube, file Bas (D-C3, part 2): the blocks and the bases of `L(H_S)`
* `S4.Def_RP_ThetaCube_TrOpen`: S4-ThetaCube, file TrOpen (D-C1, part 5): the open where the block trace identity is checked
* `S4.Def_RP_ThetaCube_TrNe`: S4-ThetaCube, file TrNe (D-C1, part 6): the open `ψ_S⁻¹ VJ` is nonempty
* `S4.Def_RP_ThetaCube_GrA`: S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
* `S4.Def_RP_DegPoly_Cube`: Degree polynomiality, part 3: the quadratic relation from the cube relation (unit S4-DegPoly)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_IntersectC_Dense =====
section

/-!
# S4-IntersectC, file Dense: translates of a separating divisor are dense (L36, O7)

* `mem_support_effI_of_pos`: a point with positive coefficient lies in `supp (effI D)`.
* `coheight_iso`: isomorphisms of schemes keep the codimension of points.
* `finite_coheight_one`: a proper closed subset of an irreducible Noetherian scheme has finitely many
  points of codimension one.
* `transl_dense`: if the right translates of `supp D` separate `k`-points, the left translates of
  `supp D` by any infinite set of `k`-points are dense.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj CartesianMonoidalCategory
  TopologicalSpace

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA
  RamanujanPetersson.IntersectB

section Top

variable {X : Scheme.{u}}

/-- A point with positive coefficient lies in the support of `effI D`. -/
lemma mem_support_effI_of_pos (D : AlgebraicCycle X ℤ) (hfin : (Function.support D).Finite)
    {z : X} (hz : 0 < D z) : z ∈ ((effI D).support : Set X) := by
  classical
  have hmem : z ∈ hfin.toFinset := hfin.mem_toFinset.mpr hz.ne'
  rw [effI_eq_prod D hfin.toFinset fun w hw => hfin.mem_toFinset.mpr hw,
    ← Finset.prod_erase_mul _ _ hmem]
  simp only [Scheme.IdealSheafData.support_mul, Closeds.coe_sup, Set.mem_union]
  right
  rw [(primeI z).support_pow _ (by omega), coe_support_primeI]
  exact subset_closure (Set.mem_singleton z)

end Top

section Dense

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

omit [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left] in
theorem ltransl_inv_apply (w : 𝟙_ (Over (Spec (.of k))) ⟶ A) (x : A.left) :
    (ltransl A w).left ((ltransl A w⁻¹).left x) = x := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ltransl_comp_ltransl, _root_.mul_inv_cancel,
    ltransl_one, Over.id_left]
  try rfl

/-- **TranslDense** (L36 a): if the right translates of `supp D` separate `k`-points, the left
translates of `supp D` by an infinite set of `k`-points are dense. -/
theorem transl_dense {D : AlgebraicCycle A.left ℤ} (hW : D ∈ weilDivisors A.left)
    (hsep : ∀ b b' : 𝟙_ (Over (Spec (.of k))) ⟶ A, b ≠ b' → ∃ a,
      pt A (b * a) ∈ ((effI D).support : Set A.left) ∧
        pt A (b' * a) ∉ ((effI D).support : Set A.left))
    (Z : Set (𝟙_ (Over (Spec (.of k))) ⟶ A)) (hZ : Z.Infinite) :
    closure (⋃ w ∈ Z, (ltransl A w).left ⁻¹' ((effI D).support : Set A.left)) = Set.univ := by
  classical
  have := noetherianSpace_left A
  have hfin : (Function.support D).Finite := support_finite_of_compact D
  by_contra hne
  have hS := isClosed_closure (s := ⋃ w ∈ Z, (ltransl A w).left ⁻¹' ((effI D).support : Set A.left))
  have hPfin : {z : A.left | 0 < D z}.Finite := hfin.subset fun z (hz : 0 < D z) => hz.ne'
  have : Finite {z : A.left | 0 < D z} := hPfin.to_subtype
  have hmaps : Set.MapsTo (fun w (z : {z : A.left | 0 < D z}) => (ltransl A w⁻¹).left z) Z
      (Set.pi Set.univ fun _ => {p | p ∈ closure (⋃ w ∈ Z, (ltransl A w).left ⁻¹'
        ((effI D).support : Set A.left)) ∧ Order.coheight p = 1}) := by
    intro w hw z _
    refine ⟨subset_closure (Set.mem_biUnion hw ?_), ?_⟩
    · show (ltransl A w).left ((ltransl A w⁻¹).left z) ∈ ((effI D).support : Set A.left)
      rw [ltransl_inv_apply]
      exact mem_support_effI_of_pos D hfin z.2
    · have := isIso_ltransl_left A w⁻¹
      show Order.coheight ((ltransl A w⁻¹).left z) = 1
      rw [coheight_iso]
      exact hW z.1 (show 0 < D z.1 from z.2).ne'
  obtain ⟨w, -, w', -, hww, heq⟩ := hZ.exists_ne_map_eq_of_mapsTo hmaps
    (Set.Finite.pi fun _ => finite_coheight_one hS hne)
  have hc : ∀ z, 0 < D z → (ltransl A (w * w'⁻¹)).left z = z := fun z hz => by
    have h : (ltransl A w⁻¹).left z = (ltransl A w'⁻¹).left z := congrFun heq ⟨z, hz⟩
    rw [← ltransl_comp_ltransl, Over.comp_left, Scheme.Hom.comp_apply, ← h, ltransl_inv_apply]
  obtain ⟨a, ha, hca⟩ := hsep 1 (w * w'⁻¹) fun h => hww (_root_.mul_inv_eq_one.mp h.symm)
  rw [_root_.one_mul] at ha
  apply hca
  rw [← ltransl_pt]
  obtain ⟨z, hz, hza⟩ := mem_support_effI D hfin ha
  have h := (specializes_iff_mem_closure.mpr hza).map (ltransl A (w * w'⁻¹)).left.continuous
  rw [hc z hz] at h
  exact h.mem_closed (effI D).support.isClosed (mem_support_effI_of_pos D hfin hz)

end Dense

end RamanujanPetersson.IntersectC


end

-- ===== S4.Def_RP_IntersectC_Pos =====
section

/-!
# S4-IntersectC, file Pos: positivity of the self-intersection (L36, O9)

* `le_coheight_closed`: closed points have codimension `≥ g` (homogeneity).
* `len_pos`: a closed subscheme with finite nonempty support has positive length.
* `zid_nonempty`: `i ≤ g` translates of `supp D` always meet, when translates separate points.
* **L36** `inum_pos`: `0 < (D^g)` for an effective Weil divisor whose translates separate points.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj CartesianMonoidalCategory
  TopologicalSpace

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA
  RamanujanPetersson.IntersectB

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- Homogeneity: closed points have codimension `≥ g` when some point has height `≥ g`. -/
theorem le_coheight_closed {g : ℕ} (hg : ∃ x : A.left, (g : ℕ∞) ≤ Order.height x) (y : A.left)
    (hy : IsClosed ({y} : Set A.left)) : (g : ℕ∞) ≤ Order.coheight y := by
  obtain ⟨x, hx⟩ := hg
  obtain ⟨p, -, hp⟩ := Order.exists_series_of_le_height x hx
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨y0, hy0, hy0c⟩ := (isClosed_closure (s := {p.head})).exists_closed_singleton
    ⟨p.head, subset_closure (Set.mem_singleton _)⟩
  obtain ⟨a, ha⟩ := exists_transl_eq A y0 y hy0c hy
  have := isIso_translL A a
  rw [← ha, coheight_iso, ← hp]
  exact Order.length_le_coheight (x := y0) (p := p)
    (show p.head ⤳ y0 from specializes_iff_mem_closure.mpr hy0)

/-- A closed subscheme with finite nonempty support has positive length. -/
theorem len_pos (J : A.left.IdealSheafData) (hfin : (J.support : Set A.left).Finite)
    (hne : (J.support : Set A.left).Nonempty) : 0 < len A J := by
  obtain ⟨V, hV⟩ := exists_affine_mem A hfin.toFinset
  have hV' : (J.support : Set A.left) ⊆ V := fun x hx => hV x (hfin.mem_toFinset.mpr hx)
  obtain ⟨hfinite, hlen⟩ := len_eq_finrank A J V hV' hfin
  let _ := (algV A V).hom.toAlgebra
  rw [hlen]
  obtain ⟨x, hx⟩ := hne
  have hxV : x ∈ (V : A.left.Opens) := hV' hx
  have hne_top : J.ideal V ≠ ⊤ := fun htop => by
    have h := (Scheme.IdealSheafData.mem_support_iff_of_mem hxV).mp hx
    rw [Scheme.mem_zeroLocus_iff] at h
    exact h 1 (by rw [htop]; exact Submodule.mem_top)
      (by rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; exact hxV)
  have : Nontrivial (Γ(A.left, V) ⧸ J.ideal V) := Ideal.Quotient.nontrivial_iff.mpr hne_top
  exact Module.finrank_pos

theorem comp_slice {i : ℕ} (a' : Fin i → (𝟙_ (Over (Spec (.of k))) ⟶ A))
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ A) : b ≫ slice A a' = ptOf A (i + 1) (Fin.snoc a' b) := by
  change b ≫ lift (toUnit A ≫ ptOf A i a') (𝟙 A) =
    lift (ptOf A i (Fin.init (Fin.snoc a' b : Fin (i + 1) → _)))
      ((Fin.snoc a' b : Fin (i + 1) → _) (Fin.last i))
  rw [Fin.init_snoc, Fin.snoc_last, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit,
    toUnit_unit, Category.id_comp]

theorem mem_supp_snoc {i : ℕ} (E : A.left.IdealSheafData)
    (a' : Fin i → (𝟙_ (Over (Spec (.of k))) ⟶ A)) (b : 𝟙_ (Over (Spec (.of k))) ⟶ A) (x : A.left) :
    x ∈ ((Zid A (fun _ => E) (Fin.snoc a' b)).support : Set A.left) ↔
      x ∈ ((Zid A (fun _ => E) a').support : Set A.left) ∧
        (transl A b).left x ∈ (E.support : Set A.left) := by
  simp only [coe_support_Zid, Set.mem_iInter, Set.mem_preimage, Fin.forall_fin_succ',
    Fin.snoc_castSucc, Fin.snoc_last]

/-- One more translate still meets the intersection (induction step of L36). -/
theorem step (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x)) {g : ℕ}
    (hg : ∃ x : A.left, (g : ℕ∞) ≤ Order.height x) {D : AlgebraicCycle A.left ℤ}
    (hW : D ∈ weilDivisors A.left)
    (hsep : ∀ b b' : 𝟙_ (Over (Spec (.of k))) ⟶ A, b ≠ b' → ∃ a,
      pt A (b * a) ∈ ((effI D).support : Set A.left) ∧
        pt A (b' * a) ∉ ((effI D).support : Set A.left))
    {i : ℕ} (hi : i < g) (a' : Fin i → (𝟙_ (Over (Spec (.of k))) ⟶ A))
    (hne : ((Zid A (fun _ => effI D) a').support : Set A.left).Nonempty)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    ((Zid A (fun _ => effI D) (Fin.snoc a' b)).support : Set A.left).Nonempty := by
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hfin : (Function.support D).Finite := support_finite_of_compact D
  have hSc := (Zid A (fun _ => effI D) a').support.isClosed
  obtain ⟨w0, hw0⟩ := exists_pt_mem A _ hSc.isLocallyClosed hne
  obtain ⟨z, hzS, hz0, hzy⟩ := pit_transl A hufd hW hfin a' hw0
    (lt_of_lt_of_le (by exact_mod_cast hi) (le_coheight_closed A hg _ (isClosed_pt A w0)))
  have hZ := infinite_pts A _ hSc hzS hzy hz0
  have := isProper_famP A (fun _ : Fin (i + 1) => effI D)
  have hT : IsClosed ((slice A a').left ⁻¹' Set.range (famP A (fun _ : Fin (i + 1) => effI D))) :=
    (famP A _).isClosedMap.isClosed_range.preimage (slice A a').left.continuous
  have hmemT : ∀ b', pt A b' ∈ (slice A a').left ⁻¹' Set.range (famP A (fun _ : Fin (i + 1) => effI D))
      ↔ ((Zid A (fun _ => effI D) (Fin.snoc a' b')).support : Set A.left).Nonempty := fun b' => by
    show (slice A a').left (pt A b') ∈ Set.range (famP A (fun _ : Fin (i + 1) => effI D)) ↔ _
    rw [← pt_comp, comp_slice, mem_range_famP_iff]
    simp only [ptOf_proj]
  have hsub : (⋃ w ∈ {w | pt A w ∈ ((Zid A (fun _ => effI D) a').support : Set A.left)},
      (ltransl A w).left ⁻¹' ((effI D).support : Set A.left)) ⊆
        (slice A a').left ⁻¹' Set.range (famP A (fun _ : Fin (i + 1) => effI D)) := by
    refine Set.iUnion₂_subset fun w hw => ?_
    have hc : IsClosed ((ltransl A w).left ⁻¹' ((effI D).support : Set A.left)) :=
      (effI D).support.isClosed.preimage (ltransl A w).left.continuous
    rw [← closure_inter_closedPoints hc]
    refine closure_minimal ?_ hT
    rintro x ⟨hx, hxc⟩
    obtain ⟨b', rfl⟩ := exists_pt_eq A x hxc
    refine (hmemT b').2 ⟨pt A w, (mem_supp_snoc A _ a' b' _).2 ⟨hw, ?_⟩⟩
    rw [transl_pt, ← ltransl_pt]
    exact hx
  have hTu := closure_minimal hsub hT
  rw [transl_dense A hW hsep _ hZ] at hTu
  exact (hmemT b).1 (hTu (Set.mem_univ _))

/-- Up to `g` translates of `supp D` always meet. -/
theorem zid_nonempty (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    {g : ℕ} (hg : ∃ x : A.left, (g : ℕ∞) ≤ Order.height x) {D : AlgebraicCycle A.left ℤ}
    (hW : D ∈ weilDivisors A.left)
    (hsep : ∀ b b' : 𝟙_ (Over (Spec (.of k))) ⟶ A, b ≠ b' → ∃ a,
      pt A (b * a) ∈ ((effI D).support : Set A.left) ∧
        pt A (b' * a) ∉ ((effI D).support : Set A.left))
    (i : ℕ) (hi : i ≤ g) (a : Fin i → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ((Zid A (fun _ => effI D) a).support : Set A.left).Nonempty := by
  induction i with
  | zero =>
    exact ⟨genericPoint A.left, by
      rw [coe_support_Zid]; exact Set.mem_iInter.mpr fun j => j.elim0⟩
  | succ i ih =>
    rw [← Fin.snoc_init_self a]
    exact step A hufd hg hW hsep (by omega) _ (ih (by omega) _) _

/-- **L36**: `0 < (D^g)` for an effective Weil divisor `D` whose translates separate points. -/
theorem inum_pos (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    {g : ℕ} (hdim : ∀ x : A.left, Order.height x ≤ g)
    (hg : ∃ x : A.left, (g : ℕ∞) ≤ Order.height x) {D : AlgebraicCycle A.left ℤ}
    (hW : D ∈ weilDivisors A.left) (hE : (effI D).support ≠ ⊤)
    (hsep : ∀ b b' : 𝟙_ (Over (Spec (.of k))) ⟶ A, b ≠ b' → ∃ a,
      pt A (b * a) ∈ ((effI D).support : Set A.left) ∧
        pt A (b' * a) ∉ ((effI D).support : Set A.left)) :
    0 < inum A g hdim (fun _ => effI D) (fun _ => hE) := by
  have := isProper_Pw A g
  obtain ⟨U, hU, hUne, hspec⟩ := inum_spec A g hdim (fun _ => effI D) (fun _ => hE)
  obtain ⟨c, hc⟩ := exists_pt_mem (Pw A g) U hU.isLocallyClosed hUne
  obtain ⟨hfin, hlen⟩ := hspec c hc
  rw [← hlen]
  exact len_pos A _ hfin (zid_nonempty A hufd hg hW hsep g le_rfl _)

end RamanujanPetersson.IntersectC


end

-- ===== S4.Def_RP_ThetaSquare_CPullOpen =====
section

/-!
# S4-ThetaSquare, file CPullOpen: `cpull` along open immersions, and monotonicity (F4)

* `ringOrd_ringEquiv`: `Ring.ord` is invariant under ring isomorphisms.
* `ord_algebraMap_stalkMap`, `ord_ffMap_openImm`: an open immersion `ι` keeps orders of vanishing
  (`ord_x (ι^* h) = ord_{ι x} h`).
* `fpull_comp_left`, `avoid_comp_left`, **`cpull_comp_openImm`**: `cpull (ι ≫ f) D x = cpull f D (ι x)`.
* `isDominant_openImm`; `cpull_mono` (`D ≤ E` near `f x`) and `cpull_le_ord` (`D ≤ div g` near `f x`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RamanujanPetersson.ThetaSquare

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing RamanujanPetersson.JacDivisors
  RamanujanPetersson.IsogDegA

universe u

section
variable {U C : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsIntegral C] [IsLocallyNoetherian C]
  (ι : U ⟶ C) [IsOpenImmersion ι]

/-- **Open immersions keep orders of stalk elements.** -/
lemma ord_algebraMap_stalkMap (x : U) (a : C.presheaf.stalk (ι x)) :
    Scheme.ord (algebraMap _ U.functionField ((ι.stalkMap x).hom a)) x =
      Scheme.ord (algebraMap _ C.functionField a) (ι x) := by
  have hco : coheight (ι x) = coheight x := ι.isOpenEmbedding.coheight_eq
  by_cases hx : coheight x = 1
  swap
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hx (hco ▸ h))]
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero, Scheme.ord_zero, Pi.zero_apply]
  have hx' : coheight (ι x) = 1 := hco.trans hx
  have : Ring.KrullDimLE 1 (C.presheaf.stalk (ι x)) := krullDimLE_of_coheight_le hx'.le
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := C.presheaf.stalk (ι x)) (mem_nonZeroDivisors_of_ne_zero ha))
  let e : C.presheaf.stalk (ι x) ≃+* U.presheaf.stalk x :=
    (asIso (ι.stalkMap x)).commRingCatIsoToRingEquiv
  have he : ∀ b, e b = (ι.stalkMap x).hom b := fun _ => rfl
  have hb : (ι.stalkMap x).hom a ≠ 0 := by
    rw [← he]
    exact (map_ne_zero_iff e e.injective).mpr ha
  have hn' : Ring.ord (U.presheaf.stalk x) ((ι.stalkMap x).hom a) = n := by
    rw [← he, ringOrd_ringEquiv]
    exact hn.symm
  rw [ord_algebraMap_stalk hx hb hn', ord_algebraMap_stalk hx' ha hn.symm]

variable [IsDominant ι]

/-- **Open immersions keep orders of rational functions**: `ord_x (ι^* h) = ord_{ι x} h`. -/
lemma ord_ffMap_openImm (h : C.functionField) (x : U) :
    Scheme.ord ((ffMap ι).hom h) x = Scheme.ord h (ι x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := C.presheaf.stalk (ι x)) h
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hB : algebraMap _ C.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  by_cases ha0 : a = 0
  · subst ha0
    simp only [map_zero, zero_div, Scheme.ord_zero, Pi.zero_apply]
  have hA : algebraMap _ C.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha0
  have k1 := Scheme.ord_mul (x := ι x) (div_ne_zero hA hB) hB
  rw [div_mul_cancel₀ _ hB] at k1
  have k2 := Scheme.ord_mul (x := x) (ffMap_ne_zero ι (div_ne_zero hA hB)) (ffMap_ne_zero ι hB)
  rw [← map_mul, div_mul_cancel₀ _ hB, ffMap_algebraMap ι x a, ffMap_algebraMap ι x b] at k2
  have ea : Scheme.ord (algebraMap _ U.functionField (ι.stalkMap x a)) x =
      Scheme.ord (algebraMap _ C.functionField a) (ι x) := ord_algebraMap_stalkMap ι x a
  have eb : Scheme.ord (algebraMap _ U.functionField (ι.stalkMap x b)) x =
      Scheme.ord (algebraMap _ C.functionField b) (ι x) := ord_algebraMap_stalkMap ι x b
  rw [ea, eb] at k2
  linarith

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (f : C ⟶ Y)

/-- `fpull` along `ι ≫ f` is `fpull` along `f` followed by `ι^*`. -/
lemma fpull_comp_left (u : Y.presheaf.stalk (f (genericPoint C))) :
    fpull (ι ≫ f) (algebraMap _ Y.functionField u) =
      (ffMap ι).hom (fpull f (algebraMap _ Y.functionField u)) := by
  have h' : ι (genericPoint U) ⤳ genericPoint C := specializes_of_eq (map_genericPoint ι)
  have hs : (ι ≫ f) (genericPoint U) ⤳ f (genericPoint C) := f.base.hom.map_specializes h'
  rw [fpull_algebraMap f u, ← algebraMap_stalkSpecializes hs u, fpull_algebraMap]
  calc ((ι ≫ f).stalkMap (genericPoint U)).hom ((Y.presheaf.stalkSpecializes hs).hom u)
      = (ι.stalkMap (genericPoint U)).hom ((f.stalkMap (ι (genericPoint U))).hom
          ((Y.presheaf.stalkSpecializes hs).hom u)) := by
        rw [Scheme.Hom.stalkMap_comp]
        rfl
    _ = (ι.stalkMap (genericPoint U)).hom ((C.presheaf.stalkSpecializes h').hom
          ((f.stalkMap (genericPoint C)).hom u)) :=
        congrArg (ι.stalkMap (genericPoint U)).hom (f.stalkSpecializes_stalkMap_apply _ _ h' u)
    _ = _ := rfl

variable [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

lemma avoid_comp_left {D : AlgebraicCycle Y ℤ} (hA : Avoid f D) : Avoid (ι ≫ f) D := by
  obtain ⟨V, hV, hξ, h0⟩ := hA
  refine ⟨V, hV, ?_, h0⟩
  show f (ι (genericPoint U)) ∈ V
  rw [map_genericPoint ι]
  exact hξ

/-- **Pull-back along `ι ≫ f` (`ι` an open immersion) is pull-back along `f` read on `U`.** -/
lemma cpull_comp_openImm {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) (x : U) :
    cpull (ι ≫ f) D x = cpull f D (ι x) := by
  have hloc : IsLocEq D ((ι ≫ f) x) (locEq D (f (ι x))) := isLocEq_locEq hD (f (ι x))
  obtain ⟨w, -, hw⟩ := exists_unit_of_isLocEq f hA (isLocEq_locEq hD (f (ι x)))
  rw [cpull_eq_of (ι ≫ f) hD (avoid_comp_left ι f hA) hloc, cpull_apply f hD hA, ← hw,
    fpull_comp_left, ord_ffMap_openImm]

end

section
variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

lemma avoid_sub {D E : AlgebraicCycle Y ℤ} (hD : Avoid f D) (hE : Avoid f E) : Avoid f (E - D) := by
  obtain ⟨V, hV, h1, h2⟩ := hD
  obtain ⟨V', hV', h1', h2'⟩ := hE
  refine ⟨V ∩ V', hV.inter hV', ⟨h1, h1'⟩, fun w hw => ?_⟩
  rw [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, h2 w hw.1, h2' w hw.2, sub_zero]

/-- **Monotonicity**: `D ≤ E` near `f x` gives `cpull f D x ≤ cpull f E x`. -/
lemma cpull_mono {D E : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hE : E ∈ weilDivisors Y)
    (hAD : Avoid f D) (hAE : Avoid f E) (x : C) (h : ∀ z : Y, z ⤳ f x → coheight z = 1 → D z ≤ E z) :
    cpull f D x ≤ cpull f E x := by
  have hED : E - D ∈ weilDivisors Y := (weilDivisors Y).sub_mem hE hD
  have hAED : Avoid f (E - D) := avoid_sub f hAD hAE
  have e : cpull f E = cpull f D + cpull f (E - D) := by
    rw [← cpull_add f hD hED hAD hAED]
    congr 1
    abel
  have hn := cpull_nonneg f hED hAED x fun z hz h1 => by
    rw [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply]
    linarith [h z hz h1]
  rw [e, Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  linarith

/-- **`D ≤ div g` near `f x`** gives `cpull f D x ≤ ord_x (f^* g)`. -/
lemma cpull_le_ord {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hAD : Avoid f D)
    {g : Y.functionField} (hg : g ≠ 0) (hA : Avoid f (div Y g)) (x : C)
    (h : ∀ z : Y, z ⤳ f x → coheight z = 1 → D z ≤ div Y g z) :
    cpull f D x ≤ Scheme.ord (fpull f g) x := by
  have := cpull_mono f hD (div_mem_weilDivisors g) hAD hA x h
  rwa [cpull_div f hg hA, div_apply] at this

end

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_ThetaX0 =====
section

/-!
# Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`

* `pullback_openImm`: the pull-back of a Weil divisor along an open immersion is its restriction;
* `tauX d`, an open immersion, dominant; `pullback_tauX_apply`: `τ_d^* Θ` is the indicator of `τ_d⁻¹ (zTheta)`;
* `exists_eta`: if `τ_d y ∈ W`, then `zTheta = τ_d η'` for some `η' ⤳ y`;
* `exists_sep`: finitely many `K`-points of `Rfin` off a finite set `S` are common zeros of an `s` that has no zero on `S`;
* `normS_mem_eta` (the upper-bound input of the plus-curve trick): if `φ(t) = 0` and some chart point `A` contains `φ`
  but no other zero of `t`, then `Nm(t)` vanishes at the point `η'` with `τ_{c_φ⁻¹} η' = zTheta`. Proof: a minimal prime
  `q ⊆ m_A` of `(Nm t)` has height `≤ 1` (Krull); every closed point of `V(Nm t)` contains a zero of `t`, so it lies on
  `τ⁻¹ W` (if that zero is `φ`, `mem_transl_W`) or on `V(Nm s)` (`s` vanishing at the other zeros, none on `A`); by
  Jacobson `q ∈ τ⁻¹ W`, and `coheight zTheta = 1` forces `τ q = zTheta`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB RamanujanPetersson.JacDivisors

universe u

section General

open CategoryTheory AlgebraicGeometry

variable {U C : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsIntegral C] [IsLocallyNoetherian C]
  [∀ y : C, UniqueFactorizationMonoid (C.presheaf.stalk y)] (ι : U ⟶ C) [IsOpenImmersion ι] [IsDominant ι]

/-- **Pull-back along an open immersion is restriction**: `(ι^* D)(x) = D(ι x)`. -/
lemma pullback_openImm {D : AlgebraicCycle C ℤ} (hD : D ∈ weilDivisors C) (x : U) :
    JacDivisors.pullback ι D x = D (ι x) := by
  obtain ⟨-, V, -, hxV, hDV⟩ := isLocEq_locEq hD (ι x)
  rw [pullback_apply ι hD, ord_ffMap_openImm, hDV (ι x) hxV, div_apply]

end General

section ThetaX0

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- A `K`-point `e ∉ S` of `Rfin` is a zero of some `s` with no zero on `S` (prime avoidance). -/
theorem exists_sep_one (S : Finset (Rfin K F →ₐ[K] K)) (e : Rfin K F →ₐ[K] K) (he : e ∉ S) :
    ∃ s : Rfin K F, e s = 0 ∧ ∀ ψ ∈ S, ψ s ≠ 0 := by
  by_contra hne
  push Not at hne
  have hsub : ((RingHom.ker (e : Rfin K F →+* K) : Ideal (Rfin K F)) : Set (Rfin K F)) ⊆
      ⋃ ψ ∈ (↑S : Set (Rfin K F →ₐ[K] K)), ((RingHom.ker (ψ : Rfin K F →+* K) : Ideal (Rfin K F)) : Set (Rfin K F)) := by
    intro s hs
    obtain ⟨ψ, hψ, h0⟩ := hne s (RingHom.mem_ker.1 hs)
    exact Set.mem_biUnion (Finset.mem_coe.2 hψ) (RingHom.mem_ker.2 h0)
  obtain ⟨ψ, hψ, hle⟩ := (Ideal.subset_union_prime e e (fun ψ _ _ _ => RingHom.ker_isPrime _)).1 hsub
  apply he
  have heψ : e = ψ := by
    ext b
    have hb : b - algebraMap K (Rfin K F) (e b) ∈ RingHom.ker (e : Rfin K F →+* K) := by
      refine RingHom.mem_ker.2 ?_
      show e (b - algebraMap K (Rfin K F) (e b)) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have h2 : ψ (b - algebraMap K (Rfin K F) (e b)) = 0 := RingHom.mem_ker.1 (hle hb)
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h2
    exact h2.symm
  rw [heψ]
  exact hψ

/-- Finitely many `K`-points off `S` are common zeros of an `s` with no zero on `S`. -/
theorem exists_sep (S T : Finset (Rfin K F →ₐ[K] K)) (hST : Disjoint S T) :
    ∃ s : Rfin K F, (∀ e ∈ T, e s = 0) ∧ ∀ ψ ∈ S, ψ s ≠ 0 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨1, fun e he => absurd he (Finset.notMem_empty e), fun ψ _ => by rw [map_one]; exact one_ne_zero⟩
  | @insert e T heT ih =>
    obtain ⟨s1, h1, h1'⟩ := ih (Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hST)
    obtain ⟨s2, h2, h2'⟩ := exists_sep_one S e (Finset.disjoint_right.1 hST (Finset.mem_insert_self _ _))
    refine ⟨s1 * s2, fun e' he' => ?_, fun ψ hψ => ?_⟩
    · rcases Finset.mem_insert.1 he' with rfl | he'
      · rw [map_mul, h2, mul_zero]
      · rw [map_mul, h1 e' he', zero_mul]
    · rw [map_mul]
      exact mul_ne_zero (h1' ψ hψ) (h2' ψ hψ)

end ThetaX0

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve2 =====
section

/-!
# Unit S4-ThetaSquare, file Curve2: the support of `D_e` on `K`-points (T4c, part 2; Riemann-Roch only)

Let `G ≥ 0` have degree `g` and `ℓ(G) = 1`, let `W0` be canonical, and let the class of `e ∈ J(K)` be
`[W0 - G] - (g - 2)[P0]`. Then (Milne III.6.7, support part):

* `one_le_ell_iff`: `ℓ(D) ≥ 1` iff the class of `D` contains an effective divisor;
* **`eff_iff_mem_supp`**: `W0 - G + [v]` is equivalent to an effective divisor iff `v ∈ supp G`
  (Riemann-Roch in degree `g - 1` and uniqueness of the effective divisor in the class of `G`);
* `ell_eq_one_of_mem`: for `v ∈ supp G` that effective divisor `E_v` is unique;
* `exists_sum_ajCls_iff`: the Riemann condition of `mem_W_fe` in divisor form;
* **`mem_W_fe_iff`**: `f_e(q) ∈ W` iff `q ∈ supp G`, for every `K`-point `q` of `X1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve2

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- `ℓ(D) ≥ 1` iff the class of `D` contains an effective divisor. -/
theorem one_le_ell_iff (D : Places.Divisor K F) :
    1 ≤ ellFK K F D ↔ ∃ E : Places.Divisor K F, 0 ≤ E ∧ clsK K F E = clsK K F D := by
  constructor
  · intro h
    have hne : LFK K F D ≠ ⊥ := by
      intro hb
      rw [ellFK_def, hb, finrank_bot] at h
      omega
    obtain ⟨f, hfL, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨PlacesK.div f + D, (mem_LFK hf).1 hfL, ?_⟩
    rw [clsK_add (K := K) (F := F), show clsK K F (PlacesK.div f) = 0 from
      (QuotientAddGroup.eq_zero_iff _).2 (div_mem_PrincK K F hf), zero_add]
  · rintro ⟨E, hE, hc⟩
    obtain ⟨f, hf, hfd⟩ := (mem_PrincK K F).1 ((clsK_eq_iff K F).1 hc.symm)
    have hfL : f ∈ LFK K F D := by
      rw [mem_LFK hf, hfd, show -D + E + D = E by abel]
      exact hE
    haveI := finiteDimensional_LFK (K := K) (F := F) D
    have hpos : 0 < finrank K (LFK K F D) :=
      Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨f, hfL⟩, fun h => hf (congrArg Subtype.val h)⟩
    rw [ellFK_def]
    omega

/-- **Riemann-Roch support lemma**: for `G ≥ 0` of degree `g` with `ℓ(G) = 1` and a canonical `W0`,
`W0 - G + [v]` is equivalent to an effective divisor iff `v ∈ supp G`. -/
theorem eff_iff_mem_supp {W0 G : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (hG : 0 ≤ G)
    (hd : G.deg = genusFK K F) (h1 : ellFK K F G = 1) (v : Place K F) :
    (∃ E : Places.Divisor K F, 0 ≤ E ∧ clsK K F E = clsK K F (W0 - G + Finsupp.single v 1)) ↔
      1 ≤ G v := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have hrr := riemannRochFK' hk hW (G - Finsupp.single v 1)
  rw [show W0 - (G - Finsupp.single v 1) = W0 - G + Finsupp.single v 1 by abel,
    PlacesK.Divisor.deg_sub, hd, deg_single_one] at hrr
  rw [← one_le_ell_iff (W0 - G + Finsupp.single v 1)]
  constructor
  · intro h
    have h2 : 1 ≤ ellFK K F (G - Finsupp.single v 1) := by omega
    obtain ⟨H, hH, hc⟩ := (one_le_ell_iff _).1 h2
    obtain ⟨f0, -, -, huniq⟩ := exists_eq_of_ell_one h1
    have hc' : clsK K F (H + Finsupp.single v 1) = clsK K F G := by
      rw [clsK_add (K := K) (F := F), hc, ← clsK_add (K := K) (F := F), sub_add_cancel]
    have hHG : H + Finsupp.single v 1 = G :=
      (huniq _ (add_nonneg hH (Finsupp.single_nonneg.2 zero_le_one)) hc').trans (huniq G hG rfl).symm
    rw [← hHG, Finsupp.add_apply, Finsupp.single_eq_same]
    have := Finsupp.le_def.1 hH v
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  · intro hv
    have hGv : 0 ≤ G - Finsupp.single v 1 := by
      rw [Finsupp.le_def]
      intro w
      rw [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h
        simpa using hv
      · simpa using Finsupp.le_def.1 hG w
    have h2 := (one_le_ell_iff (G - Finsupp.single v 1)).2 ⟨_, hGv, rfl⟩
    omega

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

end Geom

end Curve2

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve3 =====
section

/-!
# Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)

* `div_pow_of_div`, `le_ell_single`: if `div f = [Q'] - [Q]` with `Q ≠ Q'` then `ℓ(n[Q]) ≥ n + 1` for all `n`;
* **`eq_of_clsK_single`** (Abel for one point, `g ≥ 1`): `[Q] ~ [Q'] ⇒ Q = Q'`; `ajK_injective`;
* `kPl_kptO_plusX`: the place of the plus-curve point at `x` is `ptR2 x`; `kPl_chart`: the place of a chart point;
* **`exists_chart0`**: every `K`-point `q` of `X1` lies in a chart `{c0}`, at a point centered at `kPl q`;
  `xcR_ne_of_isCenter`: then `x - c0` does not vanish at that place;
* **`eq_iota2`**: if `ptR2 x` is the place of `q` (chart `{c0}` from `exists_chart0`), then `q = ι2 (kpt x)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Abel

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem div_pow_of_div {f : F} (hf : f ≠ 0) {Q Q' : Place K F}
    (hd : (PlacesK.div f : Places.Divisor K F) = -Finsupp.single Q 1 + Finsupp.single Q' 1) (n : ℕ) :
    (PlacesK.div (f ^ n) : Places.Divisor K F) = Finsupp.single Q' (n : ℤ) - Finsupp.single Q (n : ℤ) := by
  induction n with
  | zero => rw [pow_zero, divK_one, Nat.cast_zero, Finsupp.single_zero, Finsupp.single_zero, sub_self]
  | succ n ih =>
    rw [pow_succ, PlacesK.div_mul (pow_ne_zero n hf) hf, ih, hd]
    push_cast
    rw [Finsupp.single_add, Finsupp.single_add]
    abel

/-- If `[Q] ~ [Q']` with `Q ≠ Q'`, then `ℓ(n[Q]) ≥ n + 1` (powers of `f` have exact pole order `n` at `Q`). -/
theorem le_ell_single {f : F} (hf : f ≠ 0) {Q Q' : Place K F} (hne : Q ≠ Q')
    (hd : (PlacesK.div f : Places.Divisor K F) = -Finsupp.single Q 1 + Finsupp.single Q' 1) (n : ℕ) :
    n + 1 ≤ ellFK K F (Finsupp.single Q (n : ℤ)) := by
  induction n with
  | zero => rw [Nat.cast_zero, Finsupp.single_zero, ellFK_zero']
  | succ n ih =>
    have e : Finsupp.single Q ((n + 1 : ℕ) : ℤ) = Finsupp.single Q (n : ℤ) + Finsupp.single Q 1 := by
      push_cast; exact Finsupp.single_add _ _ _
    have hle : Finsupp.single Q (n : ℤ) ≤ Finsupp.single Q ((n + 1 : ℕ) : ℤ) := by
      rw [e]; exact le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one)
    have hlt : LFK K F (Finsupp.single Q (n : ℤ)) < LFK K F (Finsupp.single Q ((n + 1 : ℕ) : ℤ)) := by
      refine lt_of_le_of_ne ((ffDataK K F).LD_mono hle) fun heq => ?_
      have hmem : f ^ (n + 1) ∈ LFK K F (Finsupp.single Q ((n + 1 : ℕ) : ℤ)) := by
        rw [mem_LFK (pow_ne_zero _ hf), div_pow_of_div hf hd, sub_add_cancel]
        exact Finsupp.single_nonneg.2 (by positivity)
      rw [← heq, mem_LFK (pow_ne_zero _ hf), div_pow_of_div hf hd] at hmem
      have h := Finsupp.le_def.1 hmem Q
      have h2 : (0 : ℤ) ≤ 0 - ((n : ℤ) + 1) + n := by
        simpa [Finsupp.single_apply, hne, hne.symm] using h
      omega
    haveI := finiteDimensional_LFK (K := K) (F := F) (Finsupp.single Q ((n + 1 : ℕ) : ℤ))
    have h3 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [ellFK_def] at ih ⊢
    omega

/-- **Abel for one point**: for `g ≥ 1`, `[Q] ~ [Q']` forces `Q = Q'`. -/
theorem eq_of_clsK_single (hg : 0 < genusFK K F) {Q Q' : Place K F}
    (h : clsK K F (Finsupp.single Q 1) = clsK K F (Finsupp.single Q' 1)) : Q = Q' := by
  by_contra hne
  obtain ⟨f, hf, hd⟩ := (mem_PrincK K F).1 ((clsK_eq_iff K F).1 h)
  have h1 := le_ell_single hf hne hd (2 * genusFK K F)
  have hk := constField_eq_bot' (K := K) (F := F)
  have h2 := ellFK_eq_of_deg hk (D := Finsupp.single Q ((2 * genusFK K F : ℕ) : ℤ))
    (by rw [deg_single']; push_cast; omega)
  rw [deg_single'] at h2
  omega

end Abel

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

end Geom

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve4 =====
section

/-!
# Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))

* `exists_of_Zdiv_pos`: a place in the support of `Zdiv S` is a point of `S`;
* `exists_mem_X0`: if `ℓ(W0 - G + 2[v]) = 1` and that class contains the reduced divisor `Zdiv S`, then `v ∈ S`;
* `exists_R2pt`: a point `φ` of an `X0` point with `φ(x - c0) ≠ 0` is `ptR2 x` for a `K`-point `x` of a plus chart;
* `Zdiv_image_eq`, `eq_cE`: class bookkeeping (`e = cE · c_φ⁻¹`);
* **`Dc_eq_one`**: for `e` of class `[W0 - G] - (g-2)[P0]` and `q` with `1 ≤ G (kPl q)`, `D_e` is `1` at `q`
  (hypotheses: `ℓ(W0 - G + 2[kPl q]) = 1`, an `X0` point in that class, `f_e` avoids `Θ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve4

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

open Classical

/-- If `ℓ(W0 - G + 2[v]) = 1` (`v ∈ G`) and that class contains `Zdiv S`, then `v` is a point of `S`. -/
theorem exists_mem_X0 {W0 G : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (hG : 0 ≤ G)
    (hd : G.deg = genusFK K F) (h1 : ellFK K F G = 1) {v : Place K F} (hv : 1 ≤ G v)
    (h2 : ellFK K F (W0 - G + Finsupp.single v 2) = 1) (S : Finset (Rfin K F →ₐ[K] K))
    (hy : clsK K F (Zdiv S) = clsK K F (W0 - G + Finsupp.single v 2)) :
    ∃ φ ∈ S, v = Sum.inl (ptP φ) := by
  obtain ⟨E, hE0, hEc⟩ := (eff_iff_mem_supp hW hG hd h1 v).2 hv
  obtain ⟨f0, -, -, huniq⟩ := exists_eq_of_ell_one h2
  have e2 : W0 - G + Finsupp.single v 1 + Finsupp.single v 1 = W0 - G + Finsupp.single v 2 := by
    rw [add_assoc, ← Finsupp.single_add]
    norm_num
  have hE1 : 0 ≤ E + Finsupp.single v 1 := add_nonneg hE0 (Finsupp.single_nonneg.2 zero_le_one)
  have hc1 : clsK K F (E + Finsupp.single v 1) = clsK K F (W0 - G + Finsupp.single v 2) := by
    rw [clsK_add, hEc, ← clsK_add, e2]
  have hZ := (huniq _ (Zdiv_nonneg S) hy).trans (huniq _ hE1 hc1).symm
  have hEv := Finsupp.le_def.1 hE0 v
  have hpos : 1 ≤ Zdiv S v := by
    rw [hZ, Finsupp.add_apply, Finsupp.single_eq_same]
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hEv
    omega
  exact exists_of_Zdiv_pos hpos

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

end Geom

end Curve4

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve6 =====
section

/-!
# Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)

* `ell_two_eq_one`: for `G ≥ 0` reduced of degree `g` with `ℓ(G) = 1`, `ℓ(W0 - G + 2[v]) = 1` for every place `v`;
* `exists_cK`, `exists_c2`: the constant `K`-points of classes `[W0] - (g-2)[P0] - [Θ]` and `g[P0] - [Θ]`;
* `exists_kJ`: a `K`-point of `J` whose closed point lies in `jX0 (X0)` is `kJ yR`;
* `avoid_of_not_mem`: `e ∉ W` makes `f_e` avoid `Θ`;
* **`isGoodFor_of`**: if `e ∉ W`, `c_K e⁻¹ ∈ jX0 (X0)`, and `AJ(q)² e c_2 ∈ jX0 (X0)` whenever `f_e (q) ∈ W`, then
  `e` is good for some `G` (`IsGoodFor P0 W0 e G`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve6

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- For `G ≥ 0` reduced of degree `g` with `ℓ(G) = 1`: `ℓ(W0 - G + 2[v]) = 1` for every `v`. -/
theorem ell_two_eq_one {W0 G : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (hG : 0 ≤ G)
    (hd : G.deg = genusFK K F) (h1 : ellFK K F G = 1) (hred : ∀ v, G v ≤ 1) (v : Place K F) :
    ellFK K F (W0 - G + Finsupp.single v 2) = 1 := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have hrr := riemannRochFK' hk hW (W0 - G + Finsupp.single v 2)
  rw [show W0 - (W0 - G + Finsupp.single v 2) = G - Finsupp.single v 2 by abel,
    PlacesK.Divisor.deg_add, PlacesK.Divisor.deg_sub, hd, degFK_canonical hk hW, deg_single'] at hrr
  have h0 : ellFK K F (G - Finsupp.single v 2) = 0 := by
    by_contra hne
    obtain ⟨E, hE, hc⟩ := (one_le_ell_iff (G - Finsupp.single v 2)).1 (by omega)
    obtain ⟨f0, -, -, huniq⟩ := exists_eq_of_ell_one h1
    have hc' : clsK K F (E + Finsupp.single v 2) = clsK K F G := by
      rw [clsK_add (K := K) (F := F), hc, ← clsK_add (K := K) (F := F), sub_add_cancel]
    have hEG : E + Finsupp.single v 2 = G :=
      (huniq _ (add_nonneg hE (Finsupp.single_nonneg.2 zero_le_two)) hc').trans (huniq G hG rfl).symm
    have h2 := hred v
    rw [← hEG, Finsupp.add_apply, Finsupp.single_eq_same] at h2
    have := Finsupp.le_def.1 hE v
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  omega

end Curve6

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve8 =====
section

/-!
# Unit S4-ThetaSquare, file Curve8: points of `X1^g` (T4c (D), nonemptiness, part 1)

* `exists_pt_coord`: a `K`-point of `X1^n` with prescribed coordinates;
* `coe_sum_ajCls`, `deg_sum_single`: classes and degrees of `Σ [t_i]`;
* `exists_c3`: the constant `c_3` of class `[W0] - (g-2)[P0] - g[P0]`;
* `eM c3 : X1^g ⟶ J`, `p ↦ c_3 Φ_g(p)⁻¹`, of class `[W0 - Σ [p_i]] - (g-2)[P0]` (`cls_eM`), surjective on
  `K`-points (`eM_surj`);
* `ell_eq_one_of_not_mem`: `ℓ(G) = 1` when the class `[W0 - G] - (g-2)[P0]` is off `W`;
* `exists_t_swap`: the Riemann-Roch step for the chart condition at a coordinate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve8

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem deg_sum_single {n : ℕ} (t : Fin n → Place K F) :
    (∑ i, Finsupp.single (t i) (1 : ℤ) : Places.Divisor K F).deg = n := by
  have h := degPicK_clsK (K := K) (F := F) (∑ i, Finsupp.single (t i) (1 : ℤ))
  rw [clsK_sum, map_sum] at h
  simp only [degPicK_clsK, deg_single_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, _root_.mul_one] at h
  exact h.symm

/-- **Chart condition at a coordinate** (Riemann-Roch): for `D0 = Σ [s_i]` (`g` places) and a coordinate `j`,
some `t` with `t j = s j` has `W0 - Σ [t_i] + 2[s_j] ~ D0`. -/
theorem exists_t_swap {W0 : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (s : Fin (genusFK K F) → Place K F)
    (j : Fin (genusFK K F)) :
    ∃ t : Fin (genusFK K F) → Place K F, t j = s j ∧
      clsK K F (W0 - ∑ i, Finsupp.single (t i) 1 + Finsupp.single (s j) 2) =
        clsK K F (∑ i, Finsupp.single (s i) 1) := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have hsplit : ∑ i, Finsupp.single (s i) (1 : ℤ) =
      Finsupp.single (s j) 1 + ∑ i ∈ Finset.univ.erase j, Finsupp.single (s i) 1 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have hR : 0 ≤ ∑ i ∈ Finset.univ.erase j, (Finsupp.single (s i) (1 : ℤ) : Places.Divisor K F) :=
    Finset.sum_nonneg fun i _ => Finsupp.single_nonneg.2 zero_le_one
  obtain ⟨X, hX⟩ : ∃ X : Places.Divisor K F, X = W0 + Finsupp.single (s j) 1 - ∑ i, Finsupp.single (s i) 1 :=
    ⟨_, rfl⟩
  have hrr := riemannRochFK' hk hW X
  have hWX : W0 - X = ∑ i ∈ Finset.univ.erase j, Finsupp.single (s i) 1 := by
    rw [hX, hsplit]
    abel
  have hXd : X.deg = (genusFK K F : ℤ) - 1 := by
    rw [hX, PlacesK.Divisor.deg_sub, PlacesK.Divisor.deg_add, deg_single_one, degFK_canonical hk hW,
      deg_sum_single]
    omega
  have h1 : 1 ≤ ellFK K F (W0 - X) := (one_le_ell_iff _).2 ⟨_, hR, by rw [hWX]⟩
  rw [hXd] at hrr
  obtain ⟨E', hE', hcE'⟩ := (one_le_ell_iff X).1 (by omega)
  have hE'd : E'.deg = (genusFK K F : ℤ) - 1 := by
    have h := congrArg (degPicK K F) hcE'
    simp only [degPicK_clsK] at h
    rw [h, hXd]
  have hE : 0 ≤ E' + Finsupp.single (s j) 1 := add_nonneg hE' (Finsupp.single_nonneg.2 zero_le_one)
  obtain ⟨t', ht'⟩ := exists_sum_single_of_nonneg (genusFK K F) hE
    (by rw [PlacesK.Divisor.deg_add, hE'd, deg_single_one]; ring)
  obtain ⟨j', hj'⟩ : ∃ j', t' j' = s j := by
    by_contra hne
    simp only [not_exists] at hne
    have h0 : (E' + Finsupp.single (s j) 1 : Places.Divisor K F) (s j) = 0 := by
      rw [ht', Finsupp.finsetSum_apply]
      exact Finset.sum_eq_zero fun i _ => by rw [Finsupp.single_apply, if_neg (hne i)]
    rw [Finsupp.add_apply, Finsupp.single_eq_same] at h0
    have := Finsupp.le_def.1 hE' (s j)
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  refine ⟨fun i => t' (Equiv.swap j j' i), by simp only [Equiv.swap_apply_left, hj'], ?_⟩
  have hsum : ∑ i, Finsupp.single (t' (Equiv.swap j j' i)) (1 : ℤ) = E' + Finsupp.single (s j) 1 := by
    rw [Equiv.sum_comp (Equiv.swap j j') (fun i => Finsupp.single (t' i) (1 : ℤ)), ← ht']
  have h2 : (Finsupp.single (s j) (2 : ℤ) : Places.Divisor K F) =
      Finsupp.single (s j) 1 + Finsupp.single (s j) 1 := by
    rw [← Finsupp.single_add]
    norm_num
  rw [hsum, h2, show W0 - (E' + Finsupp.single (s j) 1) + (Finsupp.single (s j) 1 + Finsupp.single (s j) 1) =
    W0 + Finsupp.single (s j) 1 - E' by abel, clsK_sub, hcE', ← clsK_sub, hX]
  congr 1
  abel

end Curve8

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaCube_Proj =====
section

/-!
# S4-ThetaCube, T7: the projection formula and positivity for pulled-back divisors (L42 inputs)

For an abelian variety `A` (proper integral group object over an algebraically closed field) with
factorial stalks, an endomorphism `φ`, a point `b` and an effective Weil divisor `D` whose support
avoids the image of the generic point under `φ ≫ transl b`:
* `cpull_mem_weilDivisors`: the Cartier pull-back of a Weil divisor is a Weil divisor.
* `iform_cpull_comp`: `((φ ≫ τ_b)^* D)^g = deg φ · (D^g)` (projection formula, `deg φ = 0` if not dominant).
* `iform_cpull_transl`: `((τ_b)^* D)^g = (D^g)`.
* `iform_Theta_pos`: `0 < (Θ^g)` on the Jacobian.
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA
  RamanujanPetersson.IntersectB RamanujanPetersson.IntersectC RamanujanPetersson.ThetaSquare

universe u

section Weil

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

/-- The Cartier pull-back of a Weil divisor is a Weil divisor. -/
lemma cpull_mem_weilDivisors {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) :
    cpull f D ∈ weilDivisors C := fun z hz => by
  by_contra h1
  exact hz (by rw [cpull_apply f hD hA, Scheme.ord_eq_zero_of_coheight_neq_one h1])

end Weil

section Proj

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left] [IsLocallyNoetherian A.left]
  [∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x)]

omit [IsAlgClosed k] [GrpObj A] [IsLocallyNoetherian A.left] [∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x)] in
lemma support_effI_ne_top_of_weil (D : AlgebraicCycle A.left ℤ) (hD : D ∈ weilDivisors A.left) :
    (effI D).support ≠ ⊤ := by
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  exact support_effI_ne_top D hD (support_finite_of_compact D)

/-- **Projection formula** for the pull-back of an effective Weil divisor along `φ ≫ τ_b`. -/
theorem iform_cpull_comp (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g) (φ : A ⟶ A) [IsMonHom φ]
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ A) {D : AlgebraicCycle A.left ℤ} (hD : D ∈ weilDivisors A.left)
    (hD0 : ∀ z, 0 ≤ D z) (hA : Avoid (φ ≫ transl A b).left D) :
    iform A g hdim (fun _ => cpull (φ ≫ transl A b).left D) =
      (degree φ.left : ℤ) * iform A g hdim (fun _ => D) := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x) := fun x => inferInstance
  have : IsProper (φ ≫ transl A b).left := isProper_left A (φ ≫ transl A b)
  have hW' := cpull_mem_weilDivisors _ hD hA
  have h0' : ∀ z, 0 ≤ cpull (φ ≫ transl A b).left D z :=
    fun z => cpull_nonneg _ hD hA z fun w _ _ => hD0 w
  have hE := support_effI_ne_top_of_weil A D hD
  have hE' := support_effI_ne_top_of_weil A _ hW'
  have hfin := support_finite_of_compact D
  rw [effI_cpull _ hD hD0 hfin hA, Over.comp_left, Scheme.IdealSheafData.comap_comp] at hE'
  rw [iform_eq_inumZ A hufd g hdim _ (fun _ => hW') (fun _ => h0'),
    iform_eq_inumZ A hufd g hdim _ (fun _ => hD) (fun _ => hD0),
    effI_cpull _ hD hD0 hfin hA, Over.comp_left, Scheme.IdealSheafData.comap_comp,
    inumZ_of A g hdim _ (fun _ => hE'), inumZ_of A g hdim _ (fun _ => hE),
    inum_comap A g hdim (fun _ => (effI D).comap (transl A b).left)
      (fun _ => support_comap_transl_ne_top A _ hE b) φ (fun _ => hE'),
    inum_shift A g hdim (fun _ => effI D) (fun _ => hE) (fun _ => b)]
  norm_cast

/-- Translation invariance of `(D^g)` under the Cartier pull-back. -/
theorem iform_cpull_transl (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ A) {D : AlgebraicCycle A.left ℤ} (hD : D ∈ weilDivisors A.left)
    (hD0 : ∀ z, 0 ≤ D z) (hA : Avoid (transl A b).left D) :
    iform A g hdim (fun _ => cpull (transl A b).left D) = iform A g hdim (fun _ => D) := by
  have h := iform_cpull_comp A g hdim (𝟙 A) b hD hD0 (by rwa [Category.id_comp])
  rwa [Category.id_comp, Over.id_left, degree_id, Nat.cast_one, _root_.one_mul] at h

end Proj

section Theta

open Polynomial
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_IsogDegB_Frob =====
section

/-!
# S4-IsogDegB, Frobenius-type endomorphisms (lemma L28 of S4_COREB_ROUTE.md §3)

* If `π♯ : 𝒪_{A,e} → 𝒪_{A,e}` lands in the subring generated by `k` and the `p`-th powers
  (`CharP k p`), then `dπ = 1` (`dφ_eq_one_of_frob`): tangent vectors are pointed derivations, and
  these kill constants and `p`-th powers.
* For a commutative `A`, `polyEnd π F = F(π) = ∏ (π^∘n)^{F_n}` in the Hom-group; it is a
  homomorphism, `F ↦ F(π)` is additive, and `t ≫ π = 1` gives `t ≫ F(π) = t ^ F(0)`.
* Hence `dπ = 1` gives `d F(π) = F(0)`, and for `p ∤ F(0)` the map `F(π)` is a dominant separable
  isogeny with `deg F(π) = #Ker F(π)(k)` (`polyEnd_separable`).
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory IsLocalRing

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA Polynomial

universe u

section Kill

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

end Kill

section Poly

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

/-- **L28.** If `dπ = 1` then `d F(π) = F(0)`. -/
theorem dφ_polyEnd (π : A ⟶ A) [IsMonHom π] (hπ : dφ π = 1) (F : ℤ[X]) (t : Tan A) :
    dφ (polyEnd π F) t = t ^ F.coeff 0 := by
  apply Subtype.ext
  rw [dφ_val, SubgroupClass.coe_zpow]
  apply comp_polyEnd π t.1
  have h := congrArg Subtype.val (DFunLike.congr_fun hπ t)
  rwa [dφ_val, MonoidHom.one_apply, OneMemClass.coe_one] at h

theorem coeff_dφ_polyEnd (π : A ⟶ A) [IsMonHom π] (hπ : dφ π = 1) (F : ℤ[X]) (t : Tan A)
    (r : A.left.presheaf.stalk (pt A 1)) :
    coeff (dφ (polyEnd π F) t) r = (F.coeff 0 : k) * coeff t r := by
  rw [dφ_polyEnd π hπ, coeff_zpow]

theorem dφ_polyEnd_injective (π : A ⟶ A) [IsMonHom π] (hπ : dφ π = 1) (p : ℕ) [CharP k p]
    (F : ℤ[X]) (hp : ¬ (p : ℤ) ∣ F.coeff 0) : Function.Injective (dφ (polyEnd π F)) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  rw [tan_eq_one_iff] at ht ⊢
  intro r
  have h := ht r
  rw [coeff_dφ_polyEnd π hπ] at h
  have hc : (F.coeff 0 : k) ≠ 0 := fun h0 ↦ hp ((CharP.intCast_eq_zero_iff k p _).1 h0)
  exact (mul_eq_zero.1 h).resolve_left hc

/-- **L28.** If `dπ = 1` and `p ∤ F(0)`, then `F(π)` is dominant and separable with
`deg F(π) = #Ker F(π)(k)`. -/
theorem polyEnd_separable (π : A ⟶ A) [IsMonHom π] (hπ : dφ π = 1) (p : ℕ) [CharP k p]
    [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left] (F : ℤ[X])
    (hp : ¬ (p : ℤ) ∣ F.coeff 0) :
    ∃ _ : IsDominant (polyEnd π F).left,
      @Algebra.IsSeparable A.left.functionField A.left.functionField _ _
        (ffAlgebra (polyEnd π F).left) ∧
      degree (polyEnd π F).left = Nat.card (kerPts A (polyEnd π F)) :=
  separable_of_injective _ (dφ_polyEnd_injective π hπ p F hp)

theorem degree_polyEnd (π : A ⟶ A) [IsMonHom π] (hπ : dφ π = 1) (p : ℕ) [CharP k p]
    [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left] (F : ℤ[X])
    (hp : ¬ (p : ℤ) ∣ F.coeff 0) :
    degree (polyEnd π F).left = Nat.card (kerPts A (polyEnd π F)) := by
  obtain ⟨_, _, h⟩ := polyEnd_separable π hπ p F hp
  exact h

end Poly

end RamanujanPetersson.IsogDegB


end

-- ===== S4.Def_RP_ThetaCube_Zero =====
section

/-!
# S4-ThetaCube, T8z: the input `hzero` of DegPoly for the theta divisor

* `polyEnd_zero`: `0(π) = 1` (the constant map to the origin).
* `cpull_eq_zero_of_eq_one`: the Cartier pull-back along a constant map `1 ≫ τ_b` is `0`.
* `hzero_Th`: `cTh (polyEnd π 0) ∈ numKer (formTh ..)` (it is the zero cycle).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Poly

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

end Poly

section Const

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsIntegral A.left]
  [IsLocallyNoetherian A.left] [∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x)]

/-- The Cartier pull-back along a constant map is `0`. -/
lemma cpull_eq_zero_of_eq_one (φ : A ⟶ A) (hφ : φ = 1) (b : 𝟙_ (Over (Spec (.of k))) ⟶ A)
    {D : AlgebraicCycle A.left ℤ} (hD : D ∈ weilDivisors A.left) (hA : Avoid (φ ≫ transl A b).left D) :
    cpull (φ ≫ transl A b).left D = 0 := by
  subst hφ
  have hc : ∀ x y : A.left,
      ((1 : A ⟶ A) ≫ transl A b).left x = ((1 : A ⟶ A) ≫ transl A b).left y := by
    have : Subsingleton (𝟙_ (Over (Spec (.of k)))).left :=
      (inferInstance : Subsingleton (Spec (.of k)))
    intro x y
    rw [comp_transl, _root_.one_mul, Over.comp_left, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      Subsingleton.elim ((toUnit A).left x) ((toUnit A).left y)]
  obtain ⟨V, hV, hηV, h0⟩ := id hA
  ext x
  rw [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  exact cpull_eq_zero_of _ hD hA hV (by rw [hc x (genericPoint A.left)]; exact hηV) h0

end Const

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Alg =====
section

/-!
# Unit S4-ThetaCube, file Alg: pure algebra for numerical classes (obligation T6, algebra part)

* `int_eq_zero_of_dvd`: an integer divisible by every positive natural number is `0`;
* `addHom_int_eq_zero_of_divisible`, `addHom_int_eq_zero_of_torsion`: there is no nonzero additive map from a divisible
  group, or from a torsion group, to `ℤ`;
* `mem_numKer_of_add`, `mem_numKer_of_add_torsion`: a map `f : H → M` that is additive modulo `numKer I`, from a
  divisible (or torsion) group `H`, takes values in `numKer I` (used with `H = J(k)` for the translation parameter of
  `a^* Θ_x`);
* `mem_numKer_of_nsmul`: `numKer I` is saturated (`I` is `ℤ`-valued).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.DegPoly

variable {H : Type*} [AddCommGroup H]

variable {M : Type*} [AddCommGroup M] {g : ℕ}

/-- `numKer I` is saturated: `n • u ∈ numKer I` with `n ≠ 0` gives `u ∈ numKer I`. -/
theorem mem_numKer_of_nsmul (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ) {n : ℕ} (hn : 0 < n) {u : M}
    (h : n • u ∈ numKer I) : u ∈ numKer I := by
  refine mem_numKer.mpr fun w i => ?_
  have e := mem_numKer.mp h w i
  rw [← Nat.cast_smul_eq_nsmul ℤ, I.map_update_smul, smul_eq_mul] at e
  rcases mul_eq_zero.mp e with e | e
  · exact absurd (by exact_mod_cast e) hn.ne'
  · exact e

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Cube =====
section

/-!
# S4-ThetaCube, file Cube (T5a): numerical triviality of pulled-back principal multiples

* general `cpull` facts: `avoid_zero`, `cpull_zero`, `avoid_neg`, `cpull_neg`, `avoid_sub`, `cpull_sub`,
  `avoid_nsmul`, `cpull_nsmul`;
* `div_mem_numKer`: principal divisors of `J` lie in `numKer` of the intersection form;
* **`mem_numKer_of_cpull_div`**: if `n • Z = div h` on any `P` and `L : J ⟶ P` avoids `Z`, then `L^* Z ∈ numKer`
  (the interface for the J^3 cube: `P = J^3`, `L = (α, β, γ)`);
* `cubeC c p q r`: the seven-term cube combination (hom-group law `*`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section General

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

lemma avoid_zero : Avoid f (0 : AlgebraicCycle Y ℤ) :=
  ⟨Set.univ, isOpen_univ, trivial, fun _ _ => rfl⟩

lemma cpull_zero : cpull f (0 : AlgebraicCycle Y ℤ) = 0 := by
  have h := cpull_div f (one_ne_zero (α := Y.functionField))
    (by rw [JacDivisors.div_one]; exact avoid_zero f)
  rw [JacDivisors.div_one, fpull_one, JacDivisors.div_one] at h
  exact h

lemma avoid_neg {D : AlgebraicCycle Y ℤ} (hA : Avoid f D) : Avoid f (-D) := by
  obtain ⟨V, hV, h1, h2⟩ := hA
  refine ⟨V, hV, h1, fun w hw => ?_⟩
  rw [Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, h2 w hw, neg_zero]

lemma cpull_neg {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) :
    cpull f (-D) = -cpull f D := by
  have h := cpull_add f hD ((weilDivisors Y).neg_mem hD) hA (avoid_neg f hA)
  rw [add_neg_cancel, cpull_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

lemma avoid_sub {D E : AlgebraicCycle Y ℤ} (hD : Avoid f D) (hE : Avoid f E) : Avoid f (D - E) := by
  rw [sub_eq_add_neg]
  exact avoid_add f hD (avoid_neg f hE)

lemma cpull_sub {D E : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hE : E ∈ weilDivisors Y)
    (hAD : Avoid f D) (hAE : Avoid f E) : cpull f (D - E) = cpull f D - cpull f E := by
  rw [sub_eq_add_neg, cpull_add f hD ((weilDivisors Y).neg_mem hE) hAD (avoid_neg f hAE),
    cpull_neg f hE hAE, ← sub_eq_add_neg]

lemma avoid_nsmul {D : AlgebraicCycle Y ℤ} (hA : Avoid f D) (n : ℕ) : Avoid f (n • D) := by
  induction n with
  | zero => rw [zero_smul]; exact avoid_zero f
  | succ n ih => rw [succ_nsmul]; exact avoid_add f ih hA

lemma cpull_nsmul {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) (n : ℕ) :
    cpull f (n • D) = n • cpull f D := by
  induction n with
  | zero => rw [zero_smul, zero_smul, cpull_zero]
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul,
      cpull_add f ((weilDivisors Y).nsmul_mem hD n) hD (avoid_nsmul f hA n) hA, ih]

end General

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Line =====
section

/-!
# S4-ThetaCube, file Line (D-A, part LT1): the curve test for Weil divisors

Let `X` be integral, locally Noetherian, locally factorial and Jacobson, `E` a Weil divisor on `X`, `y` a point of
coheight one and `O` an open set containing `y`. Suppose that through every closed point `p ∈ O` there is a
curve `ℓ : C ⟶ X` (`ℓ x = p`, `x` of coheight one in `C`) avoiding `E` with `ℓ^* E = 0` at `x`. Then `E y = 0`.
Proof: pick a closed point `p` of `closure {y} ∩ O` off the other components of `supp E` near `y`
(Jacobson); `cpull_pos` at `x` gives `ℓ^* E x > 0` (or `< 0`).
* `not_specializes_of_coheight`: distinct points of coheight one are incomparable;
* **`eq_zero_of_test`** (one point), **`eq_zero_of_tests`** (every point of coheight one has such an `O`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry Order Topology RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare

universe u

section LineTest

variable {C X : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral X] [IsLocallyNoetherian X]
  [∀ y : X, UniqueFactorizationMonoid (X.presheaf.stalk y)]

variable [JacobsonSpace X]

/-- **Curve test at one point.** -/
theorem eq_zero_of_test {E : AlgebraicCycle X ℤ} (hE : E ∈ weilDivisors X) {y : X} (hy : coheight y = 1)
    {O : Set X} (hO : IsOpen O) (hyO : y ∈ O)
    (htest : ∀ p ∈ O, IsClosed {p} → ∃ (ℓ : C ⟶ X) (x : C), ℓ x = p ∧ coheight x = 1 ∧ Avoid ℓ E ∧
      cpull ℓ E x = 0) : E y = 0 := by
  rcases lt_trichotomy (E y) 0 with h | h | h
  · exfalso
    refine false_of_test_pos (C := C) ((weilDivisors X).neg_mem hE) hy ?_ hO hyO fun p hp hpc => ?_
    · rw [Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply]
      omega
    · obtain ⟨ℓ, x, h1, h2, h3, h4⟩ := htest p hp hpc
      refine ⟨ℓ, x, h1, h2, avoid_neg ℓ h3, ?_⟩
      rw [cpull_neg ℓ hE h3, Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, h4, neg_zero]
  · exact h
  · exact (false_of_test_pos hE hy h hO hyO htest).elim

/-- **Curve test.** A Weil divisor is `0` if every point of coheight one has a neighbourhood whose closed points
all carry an avoiding test curve along which the pull-back vanishes. -/
theorem eq_zero_of_tests {E : AlgebraicCycle X ℤ} (hE : E ∈ weilDivisors X)
    (hcov : ∀ y : X, coheight y = 1 → ∃ O : Set X, IsOpen O ∧ y ∈ O ∧ ∀ p ∈ O, IsClosed {p} →
      ∃ (ℓ : C ⟶ X) (x : C), ℓ x = p ∧ coheight x = 1 ∧ Avoid ℓ E ∧ cpull ℓ E x = 0) : E = 0 := by
  ext y
  rw [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  by_cases hy : coheight y = 1
  · obtain ⟨O, hO, hyO, ht⟩ := hcov y hy
    exact eq_zero_of_test hE hy hO hyO ht
  · by_contra h
    exact hy (hE y h)

end LineTest

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Cover =====
section

/-!
# S4-ThetaCube, file Cover (D-A, rest): the line test on `X1^n`

* `coheight_kpt_X1`: `K`-points of `X1` have codimension one (singleton chart, `Sym¹` regular of dimension one);
* **`eq_zero_of_lines`**: let `E` be a Weil divisor on `X1^n` (factorial stalks) and, for each direction `i`, `B i`
  a proper closed subset, saturated for the `i`-th lines, such that for every `K`-point `p ∉ B i` the `i`-th line
  through `p` avoids `E` and pulls `E` back to `0` at the parameter of `p`. Then `E = 0`.
  Proof: a point `y` of codimension one off some `B i` is handled by the curve test (`eq_zero_of_tests`) with the
  `i`-th lines through the closed points of `(B i)ᶜ`. If `y ∈ ⋂ B i`, then `Y = closure {y}` is a component of every
  `B i`; off the other components every line through a point of `Y` stays in `Y`, so `Y = X1^n` by `reach`, and `y`
  would be the generic point.
* `eq_zero_of_lines'`: the same with `ℓ^* E = 0` as a cycle.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Cover

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

instance isIntegral_X1O : IsIntegral (X1O K F).left := (inferInstance : IsIntegral (X1 K F))

variable {n : ℕ} [∀ y : (PP K F n).left, UniqueFactorizationMonoid ((PP K F n).left.presheaf.stalk y)]

end Cover

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_CubeZ =====
section

/-!
# S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`

* instances on `J ⊗ J` and `P := J ⊗ (J ⊗ J)`: integral, locally Noetherian, factorial stalks;
* `q1 q2 q3 : P ⟶ J` (projections), `cubeMap α β ga = lift α (lift β ga)`;
* `cubeZ P0 x0`: the seven-term combination of `(m_S ≫ τ_{x0})^* Θ` on `P`;
* **`cpull_cubeZ`**: `(α, β, ga)^* cubeZ = cubeC (φ ↦ (φ ≫ τ_{x0})^* Θ) α β ga` (seven `Avoid` hypotheses);
* `cpull_cubeZ_hom`: the same for homomorphisms, when `x0 ∉ W`;
* **`cubeC_mem_numKer`**: if a positive multiple of `cubeZ P0 x0` is principal on `P`, the cube relation holds
  numerically for `c φ := (φ ≫ τ_{x0})^* Θ` and all homomorphisms `α β ga`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section General

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

/-- `cpull` of a seven-term combination. -/
lemma cpull_cube7 {D1 D2 D3 D4 D5 D6 D7 : AlgebraicCycle Y ℤ}
    (h1 : D1 ∈ weilDivisors Y) (h2 : D2 ∈ weilDivisors Y) (h3 : D3 ∈ weilDivisors Y)
    (h4 : D4 ∈ weilDivisors Y) (h5 : D5 ∈ weilDivisors Y) (h6 : D6 ∈ weilDivisors Y)
    (h7 : D7 ∈ weilDivisors Y) (a1 : Avoid f D1) (a2 : Avoid f D2) (a3 : Avoid f D3) (a4 : Avoid f D4)
    (a5 : Avoid f D5) (a6 : Avoid f D6) (a7 : Avoid f D7) :
    cpull f (D1 - D2 - D3 - D4 + D5 + D6 + D7) =
      cpull f D1 - cpull f D2 - cpull f D3 - cpull f D4 + cpull f D5 + cpull f D6 + cpull f D7 := by
  have s12 := (weilDivisors Y).sub_mem h1 h2
  have s3 := (weilDivisors Y).sub_mem s12 h3
  have s4 := (weilDivisors Y).sub_mem s3 h4
  have s5 := (weilDivisors Y).add_mem s4 h5
  have s6 := (weilDivisors Y).add_mem s5 h6
  have b12 := avoid_sub f a1 a2
  have b3 := avoid_sub f b12 a3
  have b4 := avoid_sub f b3 a4
  have b5 := avoid_add f b4 a5
  have b6 := avoid_add f b5 a6
  rw [cpull_add f s6 h7 b6 a7, cpull_add f s5 h6 b5 a6, cpull_add f s4 h5 b4 a5, cpull_sub f s3 h4 b3 a4,
    cpull_sub f s12 h3 b12 a3, cpull_sub f h1 h2 a1 a2]

lemma avoid_cube7 {D1 D2 D3 D4 D5 D6 D7 : AlgebraicCycle Y ℤ} (a1 : Avoid f D1) (a2 : Avoid f D2)
    (a3 : Avoid f D3) (a4 : Avoid f D4) (a5 : Avoid f D5) (a6 : Avoid f D6) (a7 : Avoid f D7) :
    Avoid f (D1 - D2 - D3 - D4 + D5 + D6 + D7) :=
  avoid_add f (avoid_add f (avoid_add f (avoid_sub f (avoid_sub f (avoid_sub f a1 a2) a3) a4) a5) a6) a7

end General

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_SmPP =====
section

/-!
# S4-ThetaCube, file SmPP (D-B0, part 2): `X1` and `X1^n` are smooth, so their stalks are factorial

* `smooth_chart`: the singleton charts `Sym¹ B_c ≅ B_c` of `X1` are smooth over `K` (file SmDed);
* `smooth_X1O`: `X1 → Spec K` is smooth (smoothness is local on the source; singleton charts cover `X1`);
* `smooth_PP`: `X1^n → Spec K` is smooth (base change and composition);
* `ufd_PP`: the stalks of `X1^n` are factorial (`JacDivisors.uniqueFactorizationMonoid_stalk_of_smooth`), so the
  line test `eq_zero_of_lines` and `eq_zero_of_cpull_surj` hold with no extra hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section SmPP

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **D-B0.** The stalks of `X1^n` are factorial. -/
instance ufd_PP (n : ℕ) (y : (PP K F n).left) :
    UniqueFactorizationMonoid ((PP K F n).left.presheaf.stalk y) :=
  uniqueFactorizationMonoid_stalk_of_smooth (PP K F n).hom y

end SmPP

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_FF =====
section

/-!
# S4-ThetaCube, file FF (D-B1, part 1): the function field of `X1` is `F`

* `ffMap_Spec_algebraMap`: `Spec f` acts on fractions through `f`; `isIso_ffMap_openImm`.
* `rhoA A : Sym¹ B_A → F`, `psiA A : K(cht A) → F` (fractions), `PsiA A := psiA A ∘ ι_A^*`;
* `PsiA_eq`: chart independence; `PsiX := PsiA {0}`, `PsiA_eq_PsiX`; `PsiX_surjective`;
* `phiX : F ≃+* K(X1)` (inverse of `PsiX`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section FFSpec

end FFSpec

section FFX1

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

instance irreducibleSpace_X1c :
    IrreducibleSpace ((colimit (symDiagram K (algebraMap K[X] F X) 1) : Scheme.{u}) : Type u) :=
  irreducibleSpace_X1 K F

instance isIntegral_chtObj (A : (ChartIdx K)ᵒᵖ) :
    IsIntegral ((symDiagram K (algebraMap K[X] F X) 1).obj A) :=
  (inferInstance : IsIntegral (cht K F A))

instance isDominant_ιX1 (A : (ChartIdx K)ᵒᵖ) :
    IsDominant (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A) := by
  haveI := isOpenImmersion_ιX1 (K := K) (F := F) A
  haveI : Nonempty ((symDiagram K (algebraMap K[X] F X) 1).obj A) :=
    (inferInstance : IsIntegral (cht K F A)).nonempty
  exact isDominant_openImm _

noncomputable instance algebra_RA (A : (ChartIdx K)ᵒᵖ) : Algebra (RA K F A) (cht K F A).functionField :=
  @AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (RA K F A) (isDomain_RA A)

instance isFractionRing_RA (A : (ChartIdx K)ᵒᵖ) : IsFractionRing (RA K F A) (cht K F A).functionField :=
  @AlgebraicGeometry.functionField_isFractionRing_of_affine (RA K F A) (isDomain_RA A)

variable (K F) in
/-- Fractions of the chart `A` as elements of `F`. -/
noncomputable def psiA (A : (ChartIdx K)ᵒᵖ) : (cht K F A).functionField →+* F :=
  IsFractionRing.lift (A := RA K F A) (rhoA_injective A)

theorem psiA_algebraMap (A : (ChartIdx K)ᵒᵖ) (r : SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) :
    psiA K F A (algebraMap (RA K F A) (cht K F A).functionField r) = rhoA K F A r :=
  IsFractionRing.lift_algebraMap _ r

variable (K F) in
/-- `K(X1) → F` through the chart `A`. -/
noncomputable def PsiA (A : (ChartIdx K)ᵒᵖ) : (X1 K F).functionField →+* F :=
  (psiA K F A).comp (ffMap (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A)).hom

instance isDominant_symMap {A A' : (ChartIdx K)ᵒᵖ} (h : A ⟶ A') :
    IsDominant ((symDiagram K (algebraMap K[X] F X) 1).map h) := by
  haveI : Nonempty ((symDiagram K (algebraMap K[X] F X) 1).obj A) :=
    (inferInstance : IsIntegral (cht K F A)).nonempty
  exact isDominant_openImm _

/-- **Chart independence.** -/
theorem PsiA_eq {A A' : (ChartIdx K)ᵒᵖ} (h : A ⟶ A') : PsiA K F A = PsiA K F A' := by
  have hw := colimit.w (symDiagram K (algebraMap K[X] F X) 1) h
  have hc : ffMap (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A) =
      ffMap (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A') ≫
        ffMap ((symDiagram K (algebraMap K[X] F X) 1).map h) :=
    (ffMap_congr hw.symm).trans (ffMap_comp _ _)
  have key : ((psiA K F A).comp (ffMap ((symDiagram K (algebraMap K[X] F X) 1).map h)).hom :
      (cht K F A').functionField →+* F) = psiA K F A' := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (RA K F A'))
      (RingHom.ext fun r => ?_)
    haveI : IsDominant (Spec.map (CommRingCat.ofHom
        (chartMap (algebraMap K[X] F X) 1 (leOfHom h.unop)).toRingHom)) :=
      isDominant_symMap (K := K) (F := F) h
    have e1 : (ffMap ((symDiagram K (algebraMap K[X] F X) 1).map h)).hom
        (algebraMap (RA K F A') (cht K F A').functionField r) =
        algebraMap (RA K F A) (cht K F A).functionField (chartMap (algebraMap K[X] F X) 1 (leOfHom h.unop) r) :=
      ffMap_Spec_algebraMap (CommRingCat.ofHom (chartMap (algebraMap K[X] F X) 1 (leOfHom h.unop)).toRingHom) r
    show psiA K F A ((ffMap ((symDiagram K (algebraMap K[X] F X) 1).map h)).hom
        (algebraMap (RA K F A') (cht K F A').functionField r)) =
      psiA K F A' (algebraMap (RA K F A') (cht K F A').functionField r)
    rw [e1, psiA_algebraMap, psiA_algebraMap]
    exact rhoA_chartMap h r
  ext g
  show psiA K F A ((ffMap (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A)).hom g) =
    psiA K F A' ((ffMap (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A')).hom g)
  rw [hc, CommRingCat.hom_comp]
  exact RingHom.congr_fun key _

variable (K F) in
/-- **`K(X1) → F`** (chart independent). -/
noncomputable def PsiX : (X1 K F).functionField →+* F := PsiA K F (A0 K)

open Classical in
theorem PsiA_eq_PsiX (A : (ChartIdx K)ᵒᵖ) : PsiA K F A = PsiX K F := by
  let B : (ChartIdx K)ᵒᵖ := op ⟨A.unop.1 ∪ {0}, A.unop.2.mono Finset.subset_union_left⟩
  have h1 : B ⟶ A := (homOfLE (show A.unop ≤ B.unop from Finset.subset_union_left)).op
  have h2 : B ⟶ A0 K := (homOfLE (show (A0 K).unop ≤ B.unop from Finset.subset_union_right)).op
  rw [← PsiA_eq h1, PsiA_eq h2, PsiX]

theorem psiA_single_surjective (c : K) : Function.Surjective (psiA K F (op ⟨{c}, Finset.singleton_nonempty c⟩)) := by
  haveI := isFractionRing_chartRing_single (K := K) (F := F) c
  intro f
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := chartRing (algebraMap K[X] F X) {c}) f
  refine ⟨algebraMap (RA K F (op ⟨{c}, Finset.singleton_nonempty c⟩)) _ (diag1 (k := K) a) /
    algebraMap (RA K F (op ⟨{c}, Finset.singleton_nonempty c⟩)) _ (diag1 (k := K) b), ?_⟩
  rw [map_div₀, psiA_algebraMap, psiA_algebraMap, rhoA_diag1, rhoA_diag1]
  rfl

theorem PsiX_surjective : Function.Surjective (PsiX K F) := by
  intro f
  haveI := isOpenImmersion_ιX1 (K := K) (F := F) (A0 K)
  obtain ⟨y, rfl⟩ := psiA_single_surjective (K := K) (F := F) 0 f
  obtain ⟨g, rfl⟩ := surjective_ffMap_openImm (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (A0 K)) y
  exact ⟨g, rfl⟩

variable (K F) in
/-- **`F ≃ K(X1)`.** -/
noncomputable def phiX : F ≃+* (X1 K F).functionField :=
  (RingEquiv.ofBijective (PsiX K F) ⟨(PsiX K F).injective, PsiX_surjective⟩).symm

@[simp] theorem PsiX_phiX (f : F) : PsiX K F (phiX K F f) = f :=
  (RingEquiv.ofBijective (PsiX K F) ⟨(PsiX K F).injective, PsiX_surjective⟩).apply_symm_apply f

@[simp] theorem phiX_PsiX (g : (X1 K F).functionField) : phiX K F (PsiX K F g) = g :=
  (RingEquiv.ofBijective (PsiX K F) ⟨(PsiX K F).injective, PsiX_surjective⟩).symm_apply_apply g

end FFX1

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Ord =====
section

/-!
# S4-ThetaCube, file Ord (D-B1, part 2): orders of vanishing on `X1` are the place orders

* `val_chart_algebraMap`: on a singleton chart, the stalk valuation at `kpt ψ0` is `≤ 1` on the chart ring
  and `< 1` exactly on `ker ψ0`;
* `ord_chart_kpt`: `ord_{kpt ψ0} h = P.ord (psiA h)` for the center `P` of `ψ0`;
* **`ord_kpt`**: `ord_{q} g = (kPl q).ord (PsiX g)`; `ord_phiX_kpt`; `ord_genericPoint_X1 = 0`;
* `isClosed_of_coheight_X1`; **`eq_of_kpt_X1`**: Weil divisors on `X1` agree if they agree at `K`-points.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial
open scoped WithZero

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.JacLaw RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Ord

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem val_chart_algebraMap (c : K) (ψ0 : SymRing K (chartRing (algebraMap K[X] F X) {c}) 1 →ₐ[K] K)
    [IsDiscreteValuationRing ((cht K F (Ac K c)).presheaf.stalk (kpt ψ0))]
    (r : SymRing K (chartRing (algebraMap K[X] F X) {c}) 1) :
    (IsDiscreteValuationRing.maximalIdeal ((cht K F (Ac K c)).presheaf.stalk (kpt ψ0))).valuation
        (cht K F (Ac K c)).functionField (algebraMap (RA K F (Ac K c)) _ r) ≤ 1 ∧
      ((IsDiscreteValuationRing.maximalIdeal ((cht K F (Ac K c)).presheaf.stalk (kpt ψ0))).valuation
        (cht K F (Ac K c)).functionField (algebraMap (RA K F (Ac K c)) _ r) < 1 ↔ ψ0 r = 0) := by
  letI : Algebra (RA K F (Ac K c)) ((cht K F (Ac K c)).presheaf.stalk (kpt ψ0)) :=
    StructureSheaf.stalkAlgebra (RA K F (Ac K c)) (kpt ψ0)
  haveI : (PrimeSpectrum.asIdeal (R := RA K F (Ac K c)) (kpt ψ0)).IsPrime :=
    PrimeSpectrum.isPrime (R := RA K F (Ac K c)) (kpt ψ0)
  haveI : IsLocalization.AtPrime ((cht K F (Ac K c)).presheaf.stalk (kpt ψ0))
      (PrimeSpectrum.asIdeal (R := RA K F (Ac K c)) (kpt ψ0)) :=
    StructureSheaf.IsLocalization.to_stalk (RA K F (Ac K c)) (kpt ψ0)
  have hT : algebraMap (RA K F (Ac K c)) (cht K F (Ac K c)).functionField r =
      algebraMap ((cht K F (Ac K c)).presheaf.stalk (kpt ψ0)) (cht K F (Ac K c)).functionField
        (algebraMap (RA K F (Ac K c)) ((cht K F (Ac K c)).presheaf.stalk (kpt ψ0)) r) :=
    (StructureSheaf.toStalk_stalkSpecializes_apply (R := RA K F (Ac K c))
      ((genericPoint_spec (cht K F (Ac K c))).specializes trivial) r).symm
  rw [hT, HeightOneSpectrum.valuation_of_algebraMap]
  refine ⟨HeightOneSpectrum.intValuation_le_one _ _, ?_⟩
  rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _
    (PrimeSpectrum.asIdeal (R := RA K F (Ac K c)) (kpt ψ0)) r).trans RingHom.mem_ker

/-- **Orders on a singleton chart are place orders.** -/
theorem ord_chart_kpt (c : K) (ψ0 : SymRing K (chartRing (algebraMap K[X] F X) {c}) 1 →ₐ[K] K)
    {P : Place K F} (hP : IsCenter P (ψ0.comp diag1)) (h : (cht K F (Ac K c)).functionField) :
    Scheme.ord h (kpt ψ0) = P.ord (psiA K F (Ac K c) h) := by
  classical
  have hp : Order.coheight (kpt ψ0 : cht K F (Ac K c)) = 1 := coheight_chartPt c (kpt ψ0) (JacLaw.isClosed_kpt ψ0)
  haveI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (SymRing K (chartRing (algebraMap K[X] F X) {c}) 1)))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr (smooth_chart K F c))
  haveI : UniqueFactorizationMonoid ((cht K F (Ac K c)).presheaf.stalk (kpt ψ0)) :=
    uniqueFactorizationMonoid_stalk_of_smooth
      (Spec.map (CommRingCat.ofHom (algebraMap K (SymRing K (chartRing (algebraMap K[X] F X) {c}) 1)))) (kpt ψ0)
  haveI : IsDiscreteValuationRing ((cht K F (Ac K c)).presheaf.stalk (kpt ψ0)) :=
    isDiscreteValuationRing_stalk hp
  let v := (IsDiscreteValuationRing.maximalIdeal ((cht K F (Ac K c)).presheaf.stalk (kpt ψ0))).valuation
    (cht K F (Ac K c)).functionField
  have hv := val_chart_algebraMap (F := F) c ψ0
  let e : (cht K F (Ac K c)).functionField ≃+* F :=
    RingEquiv.ofBijective (psiA K F (Ac K c)) ⟨(psiA K F (Ac K c)).injective, psiA_single_surjective c⟩
  have he : ∀ r : SymRing K (chartRing (algebraMap K[X] F X) {c}) 1,
      e.symm (rhoA K F (Ac K c) r) = algebraMap (RA K F (Ac K c)) _ r := fun r =>
    e.symm_apply_eq.mpr (psiA_algebraMap (Ac K c) r).symm
  let w : Valuation F ℤᵐ⁰ := v.comap (e.symm : F →+* (cht K F (Ac K c)).functionField)
  have hw : ∀ r : SymRing K (chartRing (algebraMap K[X] F X) {c}) 1,
      w (rhoA K F (Ac K c) r) = v (algebraMap (RA K F (Ac K c)) _ r) := fun r => by
    show v (e.symm _) = _
    rw [he]
  have hK : ∀ a : K, a ≠ 0 → w (algebraMap K F a) = 1 := by
    intro a ha
    rw [← rhoA_algebraMap c a, hw]
    refine le_antisymm (hv _).1 (not_lt.mp fun hlt => ha ?_)
    have h0 := (hv _).2.mp hlt
    rwa [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at h0
  obtain ⟨ϖs, hϖs⟩ := IsDiscreteValuationRing.exists_irreducible ((cht K F (Ac K c)).presheaf.stalk (kpt ψ0))
  have hvϖ : v (algebraMap _ (cht K F (Ac K c)).functionField ϖs) = WithZero.exp (-1 : ℤ) := by
    have h1 : (v (algebraMap _ (cht K F (Ac K c)).functionField ϖs))⁻¹ = WithZero.exp 1 :=
      (Ring.ordFrac_eq_valuation_inv (R := (cht K F (Ac K c)).presheaf.stalk (kpt ψ0)) _).symm.trans
        (Ring.ordFrac_irreducible hϖs)
    rw [WithZero.exp_neg, ← h1, inv_inv]
  have hϖ : w (e (algebraMap _ (cht K F (Ac K c)).functionField ϖs)) = WithZero.exp (-1 : ℤ) := by
    show v (e.symm (e _)) = _
    rw [e.symm_apply_apply]
    exact hvϖ
  obtain ⟨P', hP'⟩ := exists_placeVal_eq w hK hϖ
  have hc : ∀ P'' : Place K F, placeVal P'' = w → IsCenter P'' (ψ0.comp diag1) := by
    intro P'' h''
    refine ⟨fun y => ?_, fun y => ?_⟩
    · rw [h'', ← rhoA_diag1 (Ac K c) y, hw]
      exact (hv _).1
    · rw [h'', ← rhoA_diag1 (Ac K c) y, hw, AlgHom.comp_apply]
      exact (hv _).2
  have hPP : P' = P := isCenter_unique (Finset.mem_singleton_self c) (hc P' hP') hP
  have hPw : placeVal P = w := hPP ▸ hP'
  by_cases hh : h = 0
  · subst hh
    rw [JacComplete.ord_eq_neg_log, map_zero, map_zero, WithZero.log_zero, neg_zero]
    simp only [Scheme.ord_zero, Pi.zero_apply]
  · rw [Scheme.ord_eq_iff hp hh, JacComplete.ord_eq_neg_log, hPw]
    have hvh : v h ≠ 0 := (Valuation.ne_zero_iff v).mpr hh
    have e1 : Scheme.ordHom (X := cht K F (Ac K c)) (kpt ψ0) hp h = (v h)⁻¹ :=
      Ring.ordFrac_eq_valuation_inv (R := (cht K F (Ac K c)).presheaf.stalk (kpt ψ0)) h
    have e2 : w (psiA K F (Ac K c) h) = v h := by
      show v (e.symm (e h)) = v h
      rw [e.symm_apply_apply]
    rw [e1, e2, ← WithZero.exp_eq_coe_ofAdd, WithZero.exp_neg, WithZero.exp_log hvh]

end Ord

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Slice =====
section

/-!
# S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
* `line_prj_self`, `line_prj_ne`: a line against the projections;
* `cval q g` (the constant `g(q)` as an element of `F`), **`cval_mem`**: it lies in `K`;
* `exists_stalk_of_ord`: nonnegative place order at `q` ⇒ regular at the point `q`;
* `zPP`, `detPP` (the determinant `det_k`), `sliceRow`;
* **`slice_detPP`**: `PsiX (fpull line (detPP ..)) = det (sliceRow ..)`; **`avoid_detPP`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Slice

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

instance isDominant_X1Ohom : IsDominant (X1O K F).hom :=
  ⟨fun _ => subset_closure ⟨genericPoint (X1O K F).left, Subsingleton.elim _ _⟩⟩

instance ufd_X1O (y : (X1O K F).left) : UniqueFactorizationMonoid ((X1O K F).left.presheaf.stalk y) :=
  uniqueFactorizationMonoid_stalk_of_smooth (X1O K F).hom y

/-- Constants of `X1` are constants of `F`. -/
theorem PsiX_stalkMap_hom (b : (Spec (.of K)).presheaf.stalk ((X1O K F).hom (genericPoint (X1 K F)))) :
    PsiX K F (((X1O K F).hom.stalkMap (genericPoint (X1 K F))).hom b) ∈ Set.range (algebraMap K F) := by
  haveI hD : IsDomain (CommRingCat.of K) := inferInstanceAs (IsDomain K)
  letI : Algebra (CommRingCat.of K) (Spec (.of K)).functionField :=
    @instAlgebraCarrierFunctionFieldSpec _ hD
  haveI : IsFractionRing (CommRingCat.of K) (Spec (.of K)).functionField :=
    @functionField_isFractionRing_of_affine _ hD
  obtain ⟨c, hc⟩ := (IsFractionRing.surjective_iff_isField (R := CommRingCat.of K)).mpr (Field.toIsField K)
    (algebraMap _ (Spec (.of K)).functionField b)
  have e1 : ((X1O K F).hom.stalkMap (genericPoint (X1 K F))).hom b =
      (ffMap (X1O K F).hom).hom (algebraMap _ (Spec (.of K)).functionField b) :=
    ((ffMap_algebraMap (X1O K F).hom (genericPoint (X1 K F)) b).trans (algebraMap_generic _)).symm
  rw [e1, ← hc]
  refine ⟨c, ?_⟩
  have eι := ι_toSpecK K (algebraMap K[X] F X) 1 (A0 K)
  haveI hι : IsDominant (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (A0 K) ≫
      toSpecK K (algebraMap K[X] F X) 1) := inferInstance
  haveI hS1 : IsDominant (Spec.map (CommRingCat.ofHom
      (algebraMap K (SymRing K (chartRing (algebraMap K[X] F X) (A0 K).unop.1) 1)))) := eι ▸ hι
  have e2 := (@ffMap_comp _ _ _ (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (A0 K))
    (toSpecK K (algebraMap K[X] F X) 1) _ _ _ _ (isDominant_X1Ohom (K := K) (F := F))).symm.trans (@ffMap_congr _ _ _ _ _ _ eι _ (eι ▸ hι))
  have e2' := congrArg (fun φ => φ.hom (algebraMap (CommRingCat.of K) (Spec (.of K)).functionField c)) e2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2'
  have e3 := ffMap_Spec_algebraMap (CommRingCat.ofHom
    (algebraMap K (SymRing K (chartRing (algebraMap K[X] F X) (A0 K).unop.1) 1))) c
  have hP : ∀ z, PsiX K F z = psiA K F (A0 K)
      ((ffMap (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (A0 K))).hom z) := fun z =>
    (show PsiX K F z = (psiA K F (A0 K)).comp
      (ffMap (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (A0 K))).hom z from rfl).trans
      (RingHom.comp_apply _ _ z)
  rw [hP]
  symm
  calc psiA K F (A0 K) ((ffMap (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (A0 K))).hom
        ((ffMap (X1O K F).hom).hom (algebraMap (CommRingCat.of K) (Spec (.of K)).functionField c)))
      = psiA K F (A0 K) (algebraMap (RA K F (A0 K)) (cht K F (A0 K)).functionField
          (algebraMap K (SymRing K (chartRing (algebraMap K[X] F X) (A0 K).unop.1) 1) c)) :=
        congrArg (psiA K F (A0 K)) (e2'.trans e3)
    _ = rhoA K F (A0 K) (algebraMap K _ c) := psiA_algebraMap _ _
    _ = algebraMap K F c := rhoA_algebraMap 0 c

variable (K F) in
/-- The value `g(q)` of a rational function at a `K`-point, as an element of `F` (junk `0` if `g` has a pole). -/
noncomputable def cval (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (g : (X1 K F).functionField) : F :=
  PsiX K F (fpull (C := (X1O K F).left) (Y := (X1O K F).left) (toUnit (X1O K F) ≫ q).left g)

/-- **Values are constants.** -/
theorem cval_mem (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (g : (X1 K F).functionField) :
    cval K F q g ∈ Set.range (algebraMap K F) := by
  unfold cval
  by_cases hreg : ∃ w : (X1O K F).left.presheaf.stalk ((toUnit (X1O K F) ≫ q).left (genericPoint (X1O K F).left)),
      algebraMap _ (X1O K F).left.functionField w = g
  · obtain ⟨w, rfl⟩ := hreg
    rw [fpull_algebraMap]
    have e : ((toUnit (X1O K F) ≫ q).left.stalkMap (genericPoint (X1O K F).left)).hom w =
        ((X1O K F).hom.stalkMap (genericPoint (X1 K F))).hom
          ((q.left.stalkMap ((X1O K F).hom (genericPoint (X1 K F)))).hom w) :=
      congrArg (fun t => t.hom w) (Scheme.Hom.stalkMap_comp (X1O K F).hom q.left _)
    exact (congrArg (fun t => PsiX K F t ∈ Set.range (algebraMap K F)) e).mpr (PsiX_stalkMap_hom _)
  · rw [fpull, dif_neg hreg, map_zero]
    exact ⟨0, map_zero _⟩

end Slice

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Rank =====
section

/-!
# S4-ThetaCube, file Rank (D-B4, part 1): the slices do not vanish
* `ord_sub_cval_pos`: `f - f(q)` vanishes at `q` (the 2 x 2 case of `ord_slice_pos`);
* `ord_pos_sum`: sums of functions vanishing at a place vanish there;
* `comb_mem_LFK`: a `K`-combination of the `h l` whose values vanish at the points lies in `L(H - Σ pts)`;
* **`det_ne_zero_of_ker`**, `det_ne_zero_of_ker0`: the linear algebra (rank-nullity).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Rank

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

lemma cval_one (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) : cval K F q (phiX K F 1) = 1 := by
  rw [cval, map_one, fpull_one, map_one]

end Rank

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Good =====
section

/-!
# S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
* `IsSat n i B`: `B` contains the `i`-th line through each of its `K`-points; `isSat_iUnion`, `isSat_empty`;
* `ConstAlong n i φ`: `φ` is constant along the `i`-th lines; `isSat_preimage`, closure under `≫`, `*`, `⁻¹`,
  constants, `psiE`, `epsS := psiE · x0`;
* `ne_univ_of_compl`: finitely many closed sets with nonempty complements do not cover an irreducible space;
* `exists_ne_place`: every place has a different one;
* **`bad P0 n β i x0 cK c2 A`** `= ⋃ badC`: `e_S(p) ∉ Ogood` (all `S`), `p_k = A l` (`k ≠ i`), `p_k = p_k'`
  (`k ≠ k'`, both `≠ i`), in Abel-Jacobi coordinates; **`isClosed_bad`**, **`isSat_bad`**, **`bad_ne_univ`** (when
  `x0 ∈ Ogood`), **`of_not_mem_bad`** (the three conditions at a good `K`-point).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Good

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

theorem isSat_preimage {n : ℕ} {i : Fin n} {Y : Over (Spec (.of K))} {φ : PP K F n ⟶ Y}
    (hφ : ConstAlong n i φ) (C : Set Y.left) : IsSat n i (φ.left ⁻¹' C) := by
  rintro p hp _ ⟨x, rfl⟩
  have e : φ.left ((line K F n i p).left x) = (p ≫ φ).left (IsLocalRing.closedPoint K) := by
    have h1 : φ.left ((line K F n i p).left x) = (line K F n i p ≫ φ).left x := rfl
    rw [h1, hφ p]
    exact congrArg (fun y => (p ≫ φ).left y) (Subsingleton.elim (α := Spec (.of K)) _ _)
  show φ.left ((line K F n i p).left x) ∈ C
  rw [e]
  exact hp

theorem constAlong_comp {n : ℕ} {i : Fin n} {Y Z : Over (Spec (.of K))} {φ : PP K F n ⟶ Y}
    (hφ : ConstAlong n i φ) (ψ : Y ⟶ Z) : ConstAlong n i (φ ≫ ψ) := fun p => by
  rw [← Category.assoc, hφ p]
  simp only [Category.assoc]

theorem constAlong_const (n : ℕ) (i : Fin n) {Y : Over (Spec (.of K))} (c : 𝟙_ (Over (Spec (.of K))) ⟶ Y) :
    ConstAlong n i (toUnit (PP K F n) ≫ c) := fun p => by
  have e : line K F n i p ≫ toUnit (PP K F n) = toUnit (X1O K F) ≫ p ≫ toUnit (PP K F n) := toUnit_unique _ _
  rw [← Category.assoc, e]
  simp only [Category.assoc]

/-- Finitely many closed sets with nonempty complements do not cover an irreducible space. -/
theorem ne_univ_of_compl {X : Type*} [TopologicalSpace X] [IrreducibleSpace X] {I : Type*} [Fintype I]
    (B : I → Set X) (hB : ∀ c, IsClosed (B c)) (hne : ∀ c, ∃ y, y ∉ B c) : (⋃ c, B c) ≠ Set.univ := by
  obtain ⟨y, hy⟩ := nonempty_iInter_of_open (fun c => (B c)ᶜ) (fun c => (hB c).isOpen_compl) hne
  intro h
  have hy' : y ∈ ⋃ c, B c := h ▸ Set.mem_univ y
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hy'
  exact Set.mem_iInter.mp hy c hc

/-- Every function field over `K` has a finite place. -/
theorem nonempty_finPlaceK : Nonempty (IsDedekindDomain.HeightOneSpectrum (Places.Rfin K F)) := by
  classical
  have hX : (Ideal.span {(X : K[X])}).IsPrime := (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  have hinj := FunctionField.ringOfIntegers.algebraMap_injective K F
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := Places.Rfin K F)
    (Ideal.span {(X : K[X])}) ⊥ (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  refine ⟨⟨Q, hQ, fun h => ?_⟩⟩
  rw [h, Ideal.comap_bot_of_injective _ hinj] at hQc
  exact X_ne_zero (Ideal.span_singleton_eq_bot.mp hQc.symm)

/-- Every place has a different one. -/
theorem exists_ne_place (Q : Place K F) : ∃ Q' : Place K F, Q' ≠ Q := by
  rcases Q with Q | Q
  · obtain ⟨v⟩ := PlacesK.nonempty_infPlace K F
    exact ⟨Sum.inr v, Sum.inr_ne_inl⟩
  · obtain ⟨v⟩ := nonempty_finPlaceK (K := K) (F := F)
    exact ⟨Sum.inl v, Sum.inl_ne_inr⟩

variable (n : ℕ) (β : Fin n → Fin 3) (i : Fin n) {s : ℕ} (A : Fin s → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))

end Good

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Val =====
section

/-!
# S4-ThetaCube, file Val (D-C1, part 1): values of rational functions at `K`-points
* `RegAt x G`: `G` is regular at `x` (a subring condition); `fpull_add_of`, `fpull_sub_of`, `fpull_sum_of`;
* `regAt_fpull`: regular at `(ℓ ≫ z) (η_C)` ⇒ `fpull z G` regular at `ℓ (η_C)`, `fpull ℓ (fpull z G) = fpull (ℓ ≫ z) G`;
* **`eq_zero_of_kpt`**, **`eq_of_kpt`**: on an integral scheme locally of finite type over an algebraically closed
  `K`, rational functions regular with equal values at the `K`-points of a nonempty open are equal.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory Topology RamanujanPetersson.ThetaSquare

universe u

section Reg

variable {Y : Scheme.{u}} [IsIntegral Y]

variable {C : Scheme.{u}} [IsIntegral C] (f : C ⟶ Y)

lemma fpull_add_of {G H : Y.functionField} (hG : RegAt (f (genericPoint C)) G) (hH : RegAt (f (genericPoint C)) H) :
    fpull f (G + H) = fpull f G + fpull f H := by
  obtain ⟨w, rfl⟩ := (regAt_iff _ _).mp hG
  obtain ⟨v, rfl⟩ := (regAt_iff _ _).mp hH
  rw [← map_add, fpull_algebraMap, fpull_algebraMap, fpull_algebraMap, map_add]

lemma fpull_sum_of {ι : Type*} (s : Finset ι) (G : ι → Y.functionField)
    (h : ∀ i ∈ s, RegAt (f (genericPoint C)) (G i)) :
    fpull f (∑ i ∈ s, G i) = ∑ i ∈ s, fpull f (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, ← map_zero (algebraMap (Y.presheaf.stalk (f (genericPoint C)))
      Y.functionField), fpull_algebraMap, map_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      fpull_add_of f (h a (Finset.mem_insert_self a s))
        (Subring.sum_mem _ fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

end Reg

section Comp

variable {C P X : Scheme.{u}} [IsIntegral C] [IsIntegral P] [IsIntegral X]

/-- Regularity and values along a composite. -/
lemma regAt_fpull (ℓ : C ⟶ P) (z : P ⟶ X) {G : X.functionField} (hG : RegAt ((ℓ ≫ z) (genericPoint C)) G) :
    RegAt (ℓ (genericPoint C)) (fpull z G) ∧ fpull ℓ (fpull z G) = fpull (ℓ ≫ z) G := by
  obtain ⟨v, h1, h2⟩ := fpull_fpull ℓ z G ((regAt_iff _ _).mp hG)
  refine ⟨(regAt_iff _ _).mpr ⟨v, h1⟩, ?_⟩
  rw [← h1, fpull_algebraMap, h2]

end Comp

section Agree

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **A rational function vanishing at the `K`-points of a nonempty open is zero.** -/
theorem eq_zero_of_kpt {X : Over (Spec (.of K))} [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (G : X.left.functionField) {V : Set X.left} (hV : IsOpen V) (hne : V.Nonempty)
    (h : ∀ p : 𝟙_ (Over (Spec (.of K))) ⟶ X, p.left (genericPoint _) ∈ V →
      ∃ w : X.left.presheaf.stalk (p.left (genericPoint _)), algebraMap _ X.left.functionField w = G ∧
        (p.left.stalkMap (genericPoint _)).hom w = 0) : G = 0 := by
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hpt : ∀ x ∈ closedPoints X.left, ∃ p : 𝟙_ (Over (Spec (.of K))) ⟶ X, p.left (genericPoint _) = x :=
    fun x hx => ⟨Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp _ _ _),
      pointOfClosedPoint_apply _ _ _ _⟩
  obtain ⟨x0, hx0V, hx0c⟩ := nonempty_inter_closedPoints hne hV.isLocallyClosed
  obtain ⟨p0, rfl⟩ := hpt x0 hx0c
  obtain ⟨w0, hw0, -⟩ := h p0 hx0V
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.left.presheaf w0
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  by_contra hG
  have hs : s ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hw0
    exact hG hw0.symm
  have hb : ((X.left.basicOpen s : X.left.Opens) : Set X.left).Nonempty := by
    by_contra hb
    exact hs ((basicOpen_eq_bot_iff s).mp ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp hb))
  obtain ⟨y, ⟨hyb, hyV⟩, hyc⟩ := nonempty_inter_closedPoints
    (nonempty_preirreducible_inter (X.left.basicOpen s).isOpen hV hb ⟨_, hx0V⟩)
    ((X.left.basicOpen s).isOpen.inter hV).isLocallyClosed
  obtain ⟨p1, rfl⟩ := hpt y hyc
  obtain ⟨w1, hw1, hz⟩ := h p1 hyV
  have hyU : p1.left (genericPoint _) ∈ U := X.left.basicOpen_le s hyb
  have hu : IsUnit (X.left.presheaf.germ U _ hyU s) := (X.left.mem_basicOpen s _ hyU).mp hyb
  have e : w1 = X.left.presheaf.germ U _ hyU s := by
    apply IsFractionRing.injective (X.left.presheaf.stalk _) X.left.functionField
    rw [hw1, ← hw0, Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.algebraMap_germ_eq_germToFunctionField]
  rw [e] at hz
  exact (hu.map (p1.left.stalkMap _).hom).ne_zero hz

/-- **Rational functions regular with equal values at the `K`-points of a nonempty open are equal.** -/
theorem eq_of_kpt {X : Over (Spec (.of K))} [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (G H : X.left.functionField) {V : Set X.left} (hV : IsOpen V) (hne : V.Nonempty)
    (h : ∀ p : 𝟙_ (Over (Spec (.of K))) ⟶ X, p.left (genericPoint _) ∈ V →
      RegAt (p.left (genericPoint _)) G ∧ RegAt (p.left (genericPoint _)) H ∧ fpull p.left G = fpull p.left H) :
    G = H := by
  refine sub_eq_zero.mp (eq_zero_of_kpt (G - H) hV hne fun p hp => ?_)
  obtain ⟨hG, hH, e⟩ := h p hp
  obtain ⟨w, rfl⟩ := (regAt_iff _ _).mp hG
  obtain ⟨v, rfl⟩ := (regAt_iff _ _).mp hH
  refine ⟨w - v, map_sub _ _ _, ?_⟩
  rw [fpull_algebraMap, fpull_algebraMap] at e
  rw [map_sub, e, sub_self]

end Agree

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Tr =====
section

/-!
# S4-ThetaCube, file Tr (D-C1, part 2): trace functions on `J` and their values on the chart
* `invFF_algebraMap`, `fpull_invFF`: along an open immersion `ι`, `(ffMap ι)⁻¹ H` is regular at `ι (ℓ η)` when `H` is
  regular at `ℓ η`, and `fpull (ℓ ≫ ι) ((ffMap ι)⁻¹ H) = fpull ℓ H`;
* `gff a`: a global function of `Spec R` as a rational function; `kff c := gff c` (constants on `Spec K`);
  `fpull_SpecMap_gff`: `Spec φ^* (gff a) = gff (φ a)` (and regularity);
* `trX0 f := gff (tr f)` on the chart `X0`, `trJ d f := (ffMap τ_d)⁻¹ (trX0 f) ∈ K(J)` (`f ∈ Rfin`);
* `kJ_transl_left`, **`trJ_val`**: at `kJ yR ≫ t_d`, `trJ d f` is regular with value `kff (yR (tr f))`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open Polynomial

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory Topology RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place Rfin)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.JacComplete RamanujanPetersson.IsogDegA
open RamanujanPetersson.JacDivisors

universe u

section OpenImm

variable {P U C : Scheme.{u}} [IsIntegral P] [IsIntegral U] [IsIntegral C] (ι : U ⟶ C) [IsOpenImmersion ι]
  [IsDominant ι]

instance isIso_ffMap_oi : IsIso (ffMap ι) := isIso_ffMap_openImm ι

lemma invFF_algebraMap (x : U) (v : C.presheaf.stalk (ι x)) :
    (inv (ffMap ι)).hom (algebraMap _ U.functionField ((ι.stalkMap x).hom v)) =
      algebraMap _ C.functionField v := by
  rw [← ffMap_algebraMap ι x v, ← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply]

/-- Regularity and values of `(ffMap ι)⁻¹ H` along `ℓ ≫ ι`. -/
lemma fpull_invFF (ℓ : P ⟶ U) {H : U.functionField} (hH : RegAt (ℓ (genericPoint P)) H) :
    RegAt ((ℓ ≫ ι) (genericPoint P)) ((inv (ffMap ι)).hom H) ∧
      fpull (ℓ ≫ ι) ((inv (ffMap ι)).hom H) = fpull ℓ H := by
  obtain ⟨w, rfl⟩ := (regAt_iff _ _).mp hH
  obtain ⟨v, rfl⟩ : ∃ v, (ι.stalkMap (ℓ (genericPoint P))).hom v = w :=
    ⟨(inv (ι.stalkMap (ℓ (genericPoint P)))).hom w, by
      rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]⟩
  rw [invFF_algebraMap ι (ℓ (genericPoint P)) v]
  refine ⟨(regAt_iff _ _).mpr ⟨v, rfl⟩, ?_⟩
  refine (fpull_algebraMap (ℓ ≫ ι) v).trans ?_
  rw [fpull_algebraMap ℓ, Scheme.Hom.stalkMap_comp]
  rfl

end OpenImm

section SpecVal

variable {R : Type u} [CommRing R] [IsDomain R]

instance nonempty_top_SpecD : Nonempty (⊤ : (Spec (.of R)).Opens) :=
  ⟨⟨((⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) : Spec (.of R)), trivial⟩⟩

/-- The global function `a` of `Spec R` as a rational function. -/
noncomputable def gff (a : R) : (Spec (.of R)).functionField :=
  (Spec (.of R)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (.of R)).inv.hom a)

lemma appTop_SpecMap {S : Type u} [CommRing S] (φ : R →+* S) (a : R) :
    (Scheme.ΓSpecIso (.of S)).inv.hom (φ a) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom a) :=
  congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))

/-- Pull-back of a global function along `Spec φ`. -/
lemma fpull_SpecMap_gff {S : Type u} [CommRing S] [IsDomain S] (φ : R →+* S) (a : R) :
    RegAt ((Spec.map (CommRingCat.ofHom φ)) (genericPoint (Spec (.of S)))) (gff a) ∧
      fpull (Spec.map (CommRingCat.ofHom φ)) (gff a) = gff (φ a) := by
  have hm : Spec.map (CommRingCat.ofHom φ) (genericPoint (Spec (.of S))) ∈ (⊤ : (Spec (.of R)).Opens) := trivial
  rw [gff, ← Scheme.algebraMap_germ_eq_germToFunctionField (Spec (.of R)) hm]
  refine ⟨(regAt_iff _ _).mpr ⟨_, rfl⟩, ?_⟩
  rw [fpull_algebraMap, gff, appTop_SpecMap]
  exact Scheme.Hom.germ_stalkMap_apply (Spec.map (CommRingCat.ofHom φ)) ⊤ _ trivial _

end SpecVal

section Trace

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- The constant `c` as a rational function on `Spec K`. -/
noncomputable def kff (c : K) : (𝟙_ (Over (Spec (.of K)))).left.functionField := gff (R := K) c

end Trace

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Cst =====
section

/-!
# S4-ThetaCube, file Cst (D-C1, part 3): constants and values of `phiX f` at `K`-points
* `gff_eq_toStalk`, `gff_surjective` (on `Spec` of a field), `gff_sum`;
* `PsiX_stalkMap_val`, `PsiX_fpull_kff`: `PsiX` of the constant `c` pulled back to `X1` is `algebraMap K F c`;
* `fpull_phiX_val`: `phiX f` is regular at a `K`-point `q` with `0 ≤ ord f`, with value `kff c`, `cval q (phiX f) = c`;
* **`fpull_phiX_incB`**: at `q` with `kPl q = inl (ptP φ)`, `fpull q (phiX (incB r)) = kff (φ r)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR RamanujanPetersson.JacLaw
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Gff

variable {R : Type u} [CommRing R] [IsDomain R]

instance isDomain_ofCR : IsDomain (CommRingCat.of R) := inferInstanceAs (IsDomain R)

lemma gff_eq_toStalk (c : R) : gff c = (StructureSheaf.toStalk R (genericPoint (Spec (.of R)))).hom c :=
  congrArg (fun φ => φ.hom c) (StructureSheaf.algebraMap_germ (R := R) ⊤ (genericPoint (Spec (.of R))) trivial)

lemma gff_sum {ι : Type*} (s : Finset ι) (c : ι → R) : gff (∑ i ∈ s, c i) = ∑ i ∈ s, gff (c i) := by
  unfold gff
  rw [map_sum, map_sum]

lemma gff_surjective {k : Type u} [Field k] (z : (Spec (.of k)).functionField) : ∃ c : k, gff c = z := by
  letI : Algebra (CommRingCat.of k) (Spec (.of k)).functionField :=
    @instAlgebraCarrierFunctionFieldSpec _ isDomain_ofCR
  haveI : IsFractionRing (CommRingCat.of k) (Spec (.of k)).functionField :=
    @functionField_isFractionRing_of_affine _ isDomain_ofCR
  obtain ⟨c, hc⟩ := (IsFractionRing.surjective_iff_isField (R := CommRingCat.of k)).mpr (Field.toIsField k) z
  exact ⟨c, (gff_eq_toStalk c).trans hc⟩

end Gff

section Cst

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- `PsiX` of the constant `c` (pulled back from `Spec K`) is `c`. -/
theorem PsiX_stalkMap_val (b : (Spec (.of K)).presheaf.stalk ((X1O K F).hom (genericPoint (X1 K F)))) (c : K)
    (hc : gff c = algebraMap _ (Spec (.of K)).functionField b) :
    PsiX K F (((X1O K F).hom.stalkMap (genericPoint (X1 K F))).hom b) = algebraMap K F c := by
  haveI hD : IsDomain (CommRingCat.of K) := inferInstanceAs (IsDomain K)
  letI : Algebra (CommRingCat.of K) (Spec (.of K)).functionField :=
    @instAlgebraCarrierFunctionFieldSpec _ hD
  have hc' : algebraMap (CommRingCat.of K) (Spec (.of K)).functionField c = algebraMap _ _ b :=
    (gff_eq_toStalk c).symm.trans hc
  have e1 : ((X1O K F).hom.stalkMap (genericPoint (X1 K F))).hom b =
      (ffMap (X1O K F).hom).hom (algebraMap _ (Spec (.of K)).functionField b) :=
    ((ffMap_algebraMap (X1O K F).hom (genericPoint (X1 K F)) b).trans (algebraMap_generic _)).symm
  rw [e1, ← hc']
  have eι := ι_toSpecK K (algebraMap K[X] F X) 1 (A0 K)
  haveI hι : IsDominant (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (A0 K) ≫
      toSpecK K (algebraMap K[X] F X) 1) := inferInstance
  haveI hS1 : IsDominant (Spec.map (CommRingCat.ofHom
      (algebraMap K (SymRing K (chartRing (algebraMap K[X] F X) (A0 K).unop.1) 1)))) := eι ▸ hι
  have e2 := (@ffMap_comp _ _ _ (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (A0 K))
    (toSpecK K (algebraMap K[X] F X) 1) _ _ _ _ (isDominant_X1Ohom (K := K) (F := F))).symm.trans
      (@ffMap_congr _ _ _ _ _ _ eι _ (eι ▸ hι))
  have e2' := congrArg (fun φ => φ.hom (algebraMap (CommRingCat.of K) (Spec (.of K)).functionField c)) e2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2'
  have e3 := ffMap_Spec_algebraMap (CommRingCat.ofHom
    (algebraMap K (SymRing K (chartRing (algebraMap K[X] F X) (A0 K).unop.1) 1))) c
  have hP : ∀ z, PsiX K F z = psiA K F (A0 K)
      ((ffMap (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (A0 K))).hom z) := fun z =>
    (show PsiX K F z = (psiA K F (A0 K)).comp
      (ffMap (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (A0 K))).hom z from rfl).trans
      (RingHom.comp_apply _ _ z)
  rw [hP]
  calc psiA K F (A0 K) ((ffMap (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (A0 K))).hom
        ((ffMap (X1O K F).hom).hom (algebraMap (CommRingCat.of K) (Spec (.of K)).functionField c)))
      = psiA K F (A0 K) (algebraMap (RA K F (A0 K)) (cht K F (A0 K)).functionField
          (algebraMap K (SymRing K (chartRing (algebraMap K[X] F X) (A0 K).unop.1) 1) c)) :=
        congrArg (psiA K F (A0 K)) (e2'.trans e3)
    _ = rhoA K F (A0 K) (algebraMap K _ c) := psiA_algebraMap _ _
    _ = algebraMap K F c := rhoA_algebraMap 0 c

theorem PsiX_fpull_kff (c : K) : PsiX K F (fpull (toUnit (X1O K F)).left (kff c)) = algebraMap K F c := by
  have hm : (X1O K F).hom (genericPoint (X1 K F)) ∈ (⊤ : (Spec (.of K)).Opens) := trivial
  have e : gff (R := K) c = algebraMap _ (Spec (.of K)).functionField
      ((Spec (.of K)).presheaf.germ ⊤ _ hm ((Scheme.ΓSpecIso (.of K)).inv.hom c)) :=
    (Scheme.algebraMap_germ_eq_germToFunctionField (Spec (.of K)) hm _).symm
  show PsiX K F (fpull (X1O K F).hom (gff (R := K) c)) = _
  rw [e, fpull_algebraMap]
  exact PsiX_stalkMap_val _ c e

end Cst

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_TrPP =====
section

/-!
# S4-ThetaCube, file TrPP (D-C1, part 4): the block trace identity on `X1^n`
* `blk n β S := {k | β k ∈ S}` (the coordinates multiplied in `psiS P0 n β S`);
* `trace_val`: at a `K`-point `yR` of the chart, `yR (tr f) = Σ_{ψ ∈ ptSet yR} ψ f`;
* `trPP_val`: at a `K`-point `p` of `X1^n` such that `p ≫ ψ_S` lies on the translated chart at `yR` and the block points
  `p ≫ pr_k` (`k ∈ blk`) are the distinct points of `yR`, both sides of the identity are regular with equal values;
* **`trPP`**: if this holds on a nonempty open, `ψ_S^* (trJ d f) = Σ_{k ∈ blk} pr_k^* (phiX f)` in `K(X1^n)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR RamanujanPetersson.JacLaw
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

/-- The block `{k | β k ∈ S}` of coordinates. -/
def blk (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) : Finset (Fin n) :=
  Finset.univ.filter (fun k => β k ∈ S)

section TrPP

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

end TrPP

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Bas =====
section

/-!
# S4-ThetaCube, file Bas (D-C3, part 2): the blocks and the bases of `L(H_S)`
* `b3 g : Fin (3g) → Fin 3`, three blocks of size `g` (`card_blk3`);
* `HS_apply_ne`, `deg_HS`: `H_S` lives at `P0`;
* `exists_fR`: a `K`-basis of `L(H)` inside `Rfin` when `H` has no finite part;
* **`exists_fR_HS`**: for an infinite `P0` and `r ≥ g`, a basis `h^S` of `L(H_S)` indexed by `Fin |S-block| ⊕ Fin r`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

/-- Three blocks of size `g`: `k ↦ (finProdFinEquiv.symm k).1`. -/
def b3 (g : ℕ) : Fin (3 * g) → Fin 3 := fun k => (finProdFinEquiv.symm k).1

theorem card_blk3 (g : ℕ) (b : Fin 3) : (blk (3 * g) (b3 g) {b}).card = g := by
  refine Finset.card_eq_of_equiv_fin
    { toFun := fun k => (finProdFinEquiv.symm k.1).2
      invFun := fun j => ⟨finProdFinEquiv (b, j), by
        simp only [blk, b3, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Equiv.symm_apply_apply]⟩
      left_inv := fun k => Subtype.ext ?_
      right_inv := fun j => by simp }
  have hk : (finProdFinEquiv.symm k.1).1 = b := Finset.mem_singleton.mp (Finset.mem_filter.mp k.2).2
  show finProdFinEquiv (b, (finProdFinEquiv.symm k.1).2) = k.1
  rw [show (b, (finProdFinEquiv.symm k.1).2) = finProdFinEquiv.symm k.1 from Prod.ext hk.symm rfl,
    Equiv.apply_symm_apply]

section Bas

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **A basis of `L(H)` inside `Rfin`** when `H` has no finite part. -/
theorem exists_fR {H : Places.Divisor K F} (hH : ∀ P, H (Sum.inl P) = 0) {I : Type*} [Fintype I]
    (hι : (ellFK K F H : ℤ) = Fintype.card I) (h0 : 0 < Fintype.card I) :
    ∃ fR : I → Places.Rfin K F, (∀ l, incB K F (fR l) ∈ LFK K F H) ∧
      LinearIndependent K (fun l => incB K F (fR l)) := by
  have hfr : Module.finrank K (LFK K F H) = Fintype.card I := by
    have h := hι
    norm_cast at h
  have : Module.Finite K (LFK K F H) := Module.finite_of_finrank_pos (by rw [hfr]; exact h0)
  let b := (Module.finBasisOfFinrankEq K (LFK K F H) hfr).reindex (Fintype.equivFin I).symm
  have hR : ∀ l, ∃ y : Places.Rfin K F, algebraMap (Places.Rfin K F) F y = ((b l : LFK K F H) : F) :=
    fun l => RingHom.mem_range.mp ((mem_range_iff_valuation_le_oneK _).mpr fun P => by
      have h := ((Data.mem_LD _).mp (b l).2) (Sum.inl P)
      rw [hH P, WithZero.exp_zero] at h
      exact h)
  choose fR hfR using hR
  refine ⟨fR, fun l => ?_, ?_⟩
  · show algebraMap (Places.Rfin K F) F (fR l) ∈ LFK K F H
    rw [hfR l]
    exact (b l).2
  · have e : (fun l => incB K F (fR l)) = (LFK K F H).subtype ∘ b := funext fun l => hfR l
    rw [e]
    exact b.linearIndependent.map' _ (Submodule.ker_subtype _)

variable (P0 : Place K F)

theorem HS_apply_ne (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (r : ℕ) {Q : Place K F} (hQ : Q ≠ P0) :
    HS P0 n β S r Q = 0 := by
  classical
  rw [HS, Finsupp.smul_apply, Finsupp.single_apply, if_neg fun h => hQ h.symm, smul_zero]

theorem deg_HS (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (r : ℕ) :
    (HS P0 n β S r).deg = (genusFK K F : ℤ) + r + (Finset.univ.filter (fun k => β k ∈ S)).card - 1 := by
  rw [HS, Finsupp.smul_single_one, deg_single']

/-- **The bases `h^S` of `L(H_S)`** (`P0` infinite, `r ≥ g`). -/
theorem exists_fR_HS (hP0 : ∀ P, Sum.inl P ≠ P0) (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) {r : ℕ}
    (hr : genusFK K F ≤ r) (hg : 0 < genusFK K F) :
    ∃ fR : Fin (Finset.univ.filter (fun k => β k ∈ S)).card ⊕ Fin r → Places.Rfin K F,
      (∀ l, incB K F (fR l) ∈ LFK K F (HS P0 n β S r)) ∧ LinearIndependent K (fun l => incB K F (fR l)) := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have hd := deg_HS P0 n β S r
  refine exists_fR (fun P => HS_apply_ne P0 n β S r (hP0 P)) ?_ ?_
  · rw [ellFK_eq_of_deg hk (by rw [hd]; omega), hd, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  · rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    omega

end Bas

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_TrOpen =====
section

/-!
# S4-ThetaCube, file TrOpen (D-C1, part 5): the open where the block trace identity is checked
* `jacPic_psiS`, `cls_psiS`: the class of `p ≫ ψ_S` is `[Σ_{k ∈ blk} p_k] - #blk [P0]`;
* `ell_one_of_cls`: off `W`, a degree-`g` divisor in the class `[e] + g[P0]` has `ℓ = 1`;
* `blocks_of_Zdiv`: `Zdiv T = Σ_{k ∈ s} [v k]` with `#s = #T` makes `v` a bijection onto the points of `T`;
* `VJ P0 d := {x | x d⁻¹ ∈ jX0 (X0)} \ W` (open), `exists_yR_of_mem_VJ`;
* **`hH_of_mem`**: hypothesis (H) of `trPP` at every `K`-point of `ψ_S⁻¹ VJ` (`#blk = g`, `[d] = [Θ] - g[P0]`);
* **`trPP_open`**: the block trace identity once `ψ_S⁻¹ VJ` is nonempty.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section TrOpen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

open Classical in
/-- `Zdiv T = Σ_{k ∈ s} [v k]` with `#s = #T`: each `v k` is a point `ptP (a k)`, `a` injective on `s`, `s.image a = T`. -/
theorem blocks_of_Zdiv {I : Type*} (s : Finset I) (v : I → Place K F) (T : Finset (Places.Rfin K F →ₐ[K] K))
    (hT : T.Nonempty) (h : Zdiv T = ∑ k ∈ s, Finsupp.single (v k) (1 : ℤ)) (hc : s.card = T.card) :
    ∃ a : I → (Places.Rfin K F →ₐ[K] K), (∀ k ∈ s, v k = Sum.inl (ptP (a k))) ∧ Set.InjOn a s ∧
      s.image a = T := by
  have hval : ∀ w, Zdiv T w = ∑ k ∈ s, (Finsupp.single (v k) (1 : ℤ)) w := fun w => by
    rw [h, Finsupp.finsetSum_apply]
  have hnn : ∀ (j : I) (w : Place K F), 0 ≤ (Finsupp.single (v j) (1 : ℤ)) w := fun j w => by
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num
  have hge : ∀ k ∈ s, 1 ≤ Zdiv T (v k) := fun k hk => by
    rw [hval]
    calc (1 : ℤ) = Finsupp.single (v k) (1 : ℤ) (v k) := Finsupp.single_eq_same.symm
      _ ≤ ∑ j ∈ s, Finsupp.single (v j) (1 : ℤ) (v k) :=
        Finset.single_le_sum (f := fun j => Finsupp.single (v j) (1 : ℤ) (v k)) (fun j _ => hnn j _) hk
  have hle : ∀ w, Zdiv T w ≤ 1 := by
    rintro (P | P)
    · obtain ⟨φ, rfl⟩ := exists_ptP P
      rw [Zdiv_inl_ptP]
      split_ifs <;> norm_num
    · rw [Zdiv_inr]
      norm_num
  have hpos : ∀ w : Place K F, 1 ≤ Zdiv T w → ∃ φ, φ ∈ T ∧ w = Sum.inl (ptP φ) := by
    rintro (P | P) h1
    · obtain ⟨φ, rfl⟩ := exists_ptP P
      rw [Zdiv_inl_ptP] at h1
      refine ⟨φ, ?_, rfl⟩
      by_contra hφ
      rw [if_neg hφ] at h1
      omega
    · rw [Zdiv_inr] at h1
      omega
  have hex : ∀ k ∈ s, ∃ φ, φ ∈ T ∧ v k = Sum.inl (ptP φ) := fun k hk => hpos _ (hge k hk)
  let a : I → (Places.Rfin K F →ₐ[K] K) := fun k => if hk : k ∈ s then (hex k hk).choose else hT.choose
  have ha : ∀ k ∈ s, a k ∈ T ∧ v k = Sum.inl (ptP (a k)) := fun k hk => by
    have e : a k = (hex k hk).choose := dif_pos hk
    rw [e]
    exact (hex k hk).choose_spec
  have hinj : Set.InjOn a s := by
    intro k hk k' hk' hkk
    by_contra hne
    have hv : v k' = v k := by rw [(ha k' hk').2, (ha k hk).2, hkk]
    have h2 : (2 : ℤ) ≤ Zdiv T (v k) := by
      rw [hval]
      have hsub : ({k, k'} : Finset I) ⊆ s := Finset.insert_subset hk (Finset.singleton_subset_iff.mpr hk')
      calc (2 : ℤ) = ∑ j ∈ ({k, k'} : Finset I), Finsupp.single (v j) (1 : ℤ) (v k) := by
            rw [Finset.sum_pair hne, hv, Finsupp.single_eq_same, one_add_one_eq_two]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hnn j _)
    have := hle (v k)
    omega
  refine ⟨a, fun k hk => (ha k hk).2, hinj, Finset.eq_of_subset_of_card_le (fun φ hφ => ?_) ?_⟩
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hφ
    exact (ha k hk).1
  · exact ((Finset.card_image_of_injOn hinj).trans hc).symm.le

end TrOpen

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_TrNe =====
section

/-!
# S4-ThetaCube, file TrNe (D-C1, part 6): the open `ψ_S⁻¹ VJ` is nonempty
* `VJ_nonempty`: `VJ P0 d` is a nonempty open of `J` (`J` irreducible, `W ≠ J`, translated chart);
* `exists_blocks`: a map `a` with `Σ_{k ∈ s} [a k] = Zdiv T` when `#s = #T`;
* **`psiS_VJ_nonempty`**: `ψ_S⁻¹ VJ ≠ ∅` when `#blk = g` and `[d] = [Θ] - g[P0]`;
* **`trPP_blk`**: the block trace identity `ψ_S^* trJ d f = Σ_{k ∈ blk} pr_k^* f`, unconditionally.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section TrNe

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

open Classical in
/-- A map `a` with `Σ_{k ∈ s} [a k] = Zdiv T` when `#s = #T` (a bijection `s ≃ T`). -/
theorem exists_blocks {I : Type*} (s : Finset I) (T : Finset (Places.Rfin K F →ₐ[K] K)) (hT : T.Nonempty)
    (hc : s.card = T.card) :
    ∃ a : I → (Places.Rfin K F →ₐ[K] K),
      ∑ k ∈ s, Finsupp.single (Sum.inl (ptP (a k)) : Place K F) (1 : ℤ) = Zdiv T := by
  let e : {x // x ∈ s} ≃ {x // x ∈ T} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hc])
  refine ⟨fun k => if hk : k ∈ s then (e ⟨k, hk⟩).1 else hT.choose, ?_⟩
  rw [Zdiv, ← Finset.sum_coe_sort s, ← Finset.sum_coe_sort T, ← e.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrArg (fun φ => Finsupp.single (Sum.inl (ptP φ) : Place K F) (1 : ℤ)) (dif_pos k.2)

end TrNe

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_GrA =====
section

/-!
# S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
* `fpull_eq_ffMap`, `fpull_comp_dom`: along dominant maps `fpull` is the field map `ffMap`;
* `surjective_hom_of_nonempty`, `surjective_fst_left`, `surjective_snd_left`; `surjective_prj`, `isDominant_prj`;
* `qb b` (the three projections `J^3 ⟶ J`), `isDominant_qb`, `Phi3_qb`;
* **`ffMap_Phi3_fpull`**: `Φ3^# (q_b^# G) = ψ_{b}^# G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Dom

variable {C P Y : Scheme.{u}} [IsIntegral C] [IsIntegral P] [IsIntegral Y]

/-- Along a dominant map, `fpull` is the field map `ffMap`. -/
theorem fpull_eq_ffMap (f : C ⟶ Y) [IsDominant f] (G : Y.functionField) : fpull f G = (ffMap f).hom G := by
  have key : ∀ y (_ : y = genericPoint Y), ∃ u : Y.presheaf.stalk y, algebraMap _ Y.functionField u = G := by
    rintro y rfl
    exact ⟨G, algebraMap_generic G⟩
  obtain ⟨u, rfl⟩ := key _ (map_genericPoint f)
  rw [fpull_algebraMap, ffMap_algebraMap]
  exact (algebraMap_generic _).symm

theorem fpull_comp_dom (f : C ⟶ P) (g : P ⟶ Y) [IsDominant f] [IsDominant g] (G : Y.functionField) :
    fpull (f ≫ g) G = fpull f (fpull g G) := by
  rw [fpull_eq_ffMap, fpull_eq_ffMap, fpull_eq_ffMap, ffMap_comp]
  rfl

end Dom

section GrA

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem surjective_hom_of_nonempty (X : Over (Spec (.of K))) [Nonempty X.left] : Surjective X.hom :=
  ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

theorem surjective_fst_left (A B : Over (Spec (.of K))) [Nonempty B.left] : Surjective (fst A B).left := by
  have := surjective_hom_of_nonempty B
  show Surjective (Limits.pullback.fst A.hom B.hom)
  infer_instance

variable (P0 : Place K F)

end GrA

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_DegPoly_Cube =====
section

/-!
# Degree polynomiality, part 3: the quadratic relation from the cube relation (unit S4-DegPoly)

The input `hquad` of `deg_poly_of_quad` in the form the theorem of the cube gives it (Milne, Abelian Varieties,
Cor. 5.4 and the proof of Lemma 10.12): if `Q : R → N` on an abelian group satisfies `Q 0 = 0`, the cube relation
`Q (a+b+e) - Q (a+b) - Q (a+e) - Q (b+e) + Q a + Q b + Q e = 0` and `Q (-a) = Q a` (`D` symmetric), then
`Q (n • a + b) = n² • Q a + n • B a b + Q b` with `B a b = Q (a + b) - Q a - Q b`. `quad_of_cube` states it for
`c : R → M` up to numerical equivalence (`numKer I`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.DegPoly

section Quad

variable {R N : Type*} [AddCommGroup R] [AddCommGroup N]

/-- The polarisation `B a b = Q (a + b) - Q a - Q b` of `Q`. -/
def polar (Q : R → N) (a b : R) : N := Q (a + b) - Q a - Q b

variable {Q : R → N}

end Quad

variable {M : Type*} [AddCommGroup M] {g : ℕ}

end RamanujanPetersson.DegPoly


end


