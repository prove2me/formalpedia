-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_082
-- name    : RPLib_FX_EtPBC_082
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:41:26.868183+00:00
-- url     : https://prove2.me/theorems/d5d01c4d-a93b-59ed-8b09-9e14d50b0f50
-- title:
--   Proper base change for the projective line, library file 082
-- statement:
--   File 082 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
--   * `S4.Def_RP_EtPBC_A_O2R4`: S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes
--   * `S4.Def_RP_EtPBC_A_O2KapD`: S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class
--   * `S4.Def_RP_EtPBC_A_O2Gl2j`: S4-EtPBC-A, O2 GLOB (O2Gl2j): stages S2-S3 on the charts
--   * `S4.Def_RP_EtPBC_A_O2PP3a`: S4-EtPBC-A, O2 PP' (O2PP3a): stages S2-S3 on the charts with `J` = the bad points
--   * `S4.Def_RP_EtPBC_A_O2Gen1`: S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_073
import Definitions.Def_RPLib_FX_EtPBC_075

/-!
# Proper base change for the projective line, library file 082

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
* `S4.Def_RP_EtPBC_A_O2R4`: S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes
* `S4.Def_RP_EtPBC_A_O2KapD`: S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class
* `S4.Def_RP_EtPBC_A_O2Gl2j`: S4-EtPBC-A, O2 GLOB (O2Gl2j): stages S2-S3 on the charts
* `S4.Def_RP_EtPBC_A_O2PP3a`: S4-EtPBC-A, O2 PP' (O2PP3a): stages S2-S3 on the charts with `J` = the bad points
* `S4.Def_RP_EtPBC_A_O2Gen1`: S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2S1 =====
section

/-!
# S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes

* `opEt_ext` (maps into `opEt U` are unique), `toOpEt`, `opEtMap`, `freeMap_id`;
* `mvC_shortExact'`: the MV criterion with "surjective onto the fibre of `Z`" instead of "nonempty";
* `locC`, **`locC_shortExact`**: the one-point MV complex `Λ[D ×_P Uo] ⟶ Λ[D] ⊞ Λ[P ∖ z] ⟶ Λ[P]` for an etale `D`
  with one geometric point over `z` and all other points over `Uo` (`Uo ⊆ P ∖ z`);
* `IsLoc Λ F z β` (one-point MV class `ε_loc ∘ κ`), `locSpan Λ F` (the subgroup they generate);
* `exists_good_one`, **`split_step`** (a class dying on `U` differs from a one-point class at `z ∉ U` by a class
  dying on `U ∪ {z}`), **`mem_locSpan_of_dies`** (induction on `#(P ∖ U)`), **`mem_locSpan_P1`**:
  `H²(P¹, F) = locSpan` (with `claimD`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtPBC.GenGeo

universe u

section Gen

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

/-- **Split step**: a class dying on `U` is a one-point class at `z ∉ U` plus a class dying on `U ∪ {z}`. -/
theorem split_step (F : EtSh Λ P) (β : Ext.{u} (freeSh Λ (etId P)) F 2) (U Up Uz : P.Opens) (z : P)
    (hzU : z ∉ U) (hUp : ∀ x : P, x ∈ Up ↔ x ∈ U ∨ x = z) (hz : ∀ x : P, x ∈ Uz ↔ x ≠ z)
    (hZf : ((U : Set P)ᶜ).Finite) (hZc : ∀ x ∈ (U : Set P)ᶜ, IsClosed ({x} : Set P)) (hG : Subsingleton (Gal z))
    (hβ : (Ext.mk₀ (freeMap Λ (toTop (opEt U)))).comp β (zero_add 2) = 0) :
    ∃ γ, IsLoc Λ F z γ ∧ (Ext.mk₀ (freeMap Λ (toTop (opEt Up)))).comp (β - γ) (zero_add 2) = 0 := by
  obtain ⟨N, a, n, -, hN⟩ := local_vanish z (topPt z) 1 F β
  obtain ⟨V, hVs, hVn, hVr⟩ := exists_good_one ((U : Set P)ᶜ) hZf hZc z hzU hG N n
  have hDr : ∀ v : (opn N V).left, (opn N V).hom v ∈ U ∨ (opn N V).hom v = z := fun v => by
    rcases hVr v with h | h
    · exact Or.inl (not_not.1 h)
    · exact Or.inr h
  have hUUz : U ≤ Uz := fun x hx => (hz x).2 (fun h => hzU (h ▸ hx))
  have hUUp : U ≤ Up := fun x hx => (hUp x).2 (Or.inl hx)
  let dU : opn N V ⟶ opEt Up := toOpEt (opn N V) Up (fun v => (hUp _).2 (hDr v))
  have hS : (mvC Λ (prW (opn N V) (opEt U)) (prT (opn N V) (opEt U)) dU (opEtMap hUUp)
      (opEt_ext _ _)).ShortExact := by
    refine mvC_shortExact' _ _ _ _ _ (fun x => inferInstance) (fun x => ?_) (fun x => ?_)
    · by_cases hx : x ∈ U
      · obtain ⟨t⟩ := nonempty_fib_opEt U x hx
        exact Or.inr ⟨inferInstance, prW_bijective (opn N V) (opEt U) x t⟩
      · have hE : IsEmpty ((geomPtAt x).point.fiber.obj (opEt U)) := ⟨fun b => hx (mem_of_fib_opEt U x b)⟩
        refine Or.inl ⟨?_, prT_bijective (opn N V) (opEt U) x hE⟩
        by_cases hxz : x = z
        · rw [hxz]
          exact hVs
        · have := isEmpty_fib_of_range (opn N V) U z hDr x hx hxz
          exact ⟨fun c _ => (IsEmpty.false c).elim⟩
    · by_cases hx : x ∈ U
      · obtain ⟨t⟩ := nonempty_fib_opEt U x hx
        exact Or.inr (fun _ => ⟨t, Subsingleton.elim _ _⟩)
      · by_cases hxz : x = z
        · rw [hxz]
          obtain ⟨d⟩ := hVn
          exact Or.inl (fun _ => ⟨d, Subsingleton.elim _ _⟩)
        · have hE : IsEmpty ((geomPtAt x).point.fiber.obj (opEt Up)) :=
            ⟨fun b => ((hUp x).1 (mem_of_fib_opEt Up x b)).elim hx hxz⟩
          exact Or.inl (fun s => (IsEmpty.false s).elim)
  have hD0 : (Ext.mk₀ (freeMap Λ (toTop (opn N V)))).comp β (zero_add 2) = 0 := by
    have e1 : freeMap Λ (toTop (opn N V)) = freeMap Λ (opnι N V) ≫ freeMap Λ a := by
      rw [← freeMap_comp, toTop_ext (opnι N V ≫ a) (toTop (opn N V))]
    rw [e1, ← Ext.mk₀_comp_mk₀_assoc]
    exact (congrArg (fun t => (Ext.mk₀ (freeMap Λ (opnι N V))).comp t (zero_add 2)) hN).trans
      (Ext.comp_zero _ _ _ _ _)
  have hw : (Ext.mk₀ (freeMap Λ dU)).comp
      ((Ext.mk₀ (freeMap Λ (toTop (opEt Up)))).comp β (zero_add 2)) (zero_add 2) = 0 := by
    rw [Ext.mk₀_comp_mk₀_assoc, ← freeMap_comp, toTop_ext (dU ≫ toTop (opEt Up)) (toTop (opn N V))]
    exact hD0
  have hv : (Ext.mk₀ (freeMap Λ (opEtMap hUUp))).comp
      ((Ext.mk₀ (freeMap Λ (toTop (opEt Up)))).comp β (zero_add 2)) (zero_add 2) = 0 := by
    rw [Ext.mk₀_comp_mk₀_assoc, ← freeMap_comp, toTop_ext (opEtMap hUUp ≫ toTop (opEt Up)) (toTop (opEt U))]
    exact hβ
  obtain ⟨κ, hκ⟩ := mv_exists hS F (show 1 + 1 = 2 from rfl) _ hw hv
  let hL := locC_shortExact (Λ := Λ) (opn N V) hUUz z hz hVs hVn hDr
  refine ⟨hL.extClass.comp κ (show 1 + 1 = 2 from rfl), ⟨U, Uz, hUUz, hz, opn N V, hVs, hVn, hDr, κ, rfl⟩, ?_⟩
  have hnat := mv_naturality (𝟙 _) (𝟙 _) (opEtMap hUUz) (toTop (opEt Up))
    (by rw [Category.id_comp, Category.comp_id]) (Category.id_comp _) (toTop_ext _ _) (toTop_ext _ _) hS hL
  rw [freeMap_id, Ext.comp_mk₀_id] at hnat
  have hA : (Ext.mk₀ (freeMap Λ (toTop (opEt Up)))).comp (hL.extClass.comp κ (show 1 + 1 = 2 from rfl))
      (zero_add 2) = ((Ext.mk₀ (freeMap Λ (toTop (opEt Up)))).comp hL.extClass (zero_add 1)).comp κ
        (show 1 + 1 = 2 from rfl) :=
    (Ext.comp_assoc _ _ _ (zero_add 1) rfl rfl).symm
  rw [sub_eq_add_neg, Ext.comp_add, Ext.comp_neg, hA, ← hnat, hκ, add_neg_cancel]

end Gen

section P1

end P1

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2R4 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes

* `ext_comp_sum`, `ext_sum_comp`, `ext_mk₀_sum` (finite sums and `Ext`);
* `locLe`, `locRng`; `extClass_loc_eq`: the one-point class at `z k` is the multi-point MV class followed by
  `copPr k` (naturality along `mvLocHom`);
* **`relation_sum`**: `Σ_k ε_loc(S k) ∘ (Λ[S k ×_P U₀ ⟶ U₀]^* κ) = 0` for every `κ ∈ Ext¹(Λ[U₀], F)`;
* `isLoc_relation_term`: each summand is a one-point class (`IsLoc`) at `z k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe w u

section ExtSum

end ExtSum

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  (S : ι → P.Etale) (U₀ : P.Opens)
  (z : ι → P) (hzi : Function.Injective z) (hU : ∀ x : P, x ∈ U₀ ↔ ∀ k, x ≠ z k)
  (hD : ∀ k, Subsingleton ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDn : ∀ k, Nonempty ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDr : ∀ k (v : (S k).left), (S k).hom v ∈ U₀ ∨ (S k).hom v = z k)
  (Uz : ι → P.Opens) (hz : ∀ k (x : P), x ∈ Uz k ↔ x ≠ z k)

include hzi hU hD hDn hDr hz in
/-- Each summand of `relation_sum` is a one-point class at `z k`. -/
theorem isLoc_relation_term {F : EtSh Λ P} (κ : Ext.{u} (freeSh Λ (opEt U₀)) F 1) (k : ι) :
    IsLoc Λ F (z k) ((locC_shortExact (Λ := Λ) (S k) (locLe U₀ z hU Uz hz k) (z k) (hz k) (hD k) (hDn k)
      (hDr k)).extClass.comp ((Ext.mk₀ (freeMap Λ (prT (S k) (opEt U₀)))).comp κ (zero_add 1))
        (show 1 + 1 = 2 from rfl)) :=
  ⟨U₀, Uz k, locLe U₀ z hU Uz hz k, hz k, S k, hD k, hDn k, hDr k, _, rfl⟩

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2KapD =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class

* **`resLE_kapS_sum`**: the global class `Σ_Q kapS Q (χ Q)` restricts to `κ(χ Q)` on the piece `Q`;
* **`resLE_kapS_kumD_eq`**: for etale `f : X₁ ⟶ X`, `g : X₁ ⟶ Y` of affine schemes whose rings are finite products of
  Dedekind domains, `resLE f (kapS p (kumD α)) = resLE g c_Y` when `c_Y` is the Kummer class of a unit `H` of `Γ(Y)`
  (piecewise), `α ^ d = u`, the roots of unity match, and on every piece `p₁` of `X₁`: over `p`, `u = H · v ^ d`;
  over another piece of `X`, `H` is a `d`-th power.
  Proof: `h1_eq_zero_of_pieces` on `X₁`, `piHom_comp_eq` for `f` and `g`, `resLE_kapS_self/ne`, `resLE_kumD_eq`
  (O2KapN) and `resLE_kumD_eq_zero` (O2KapF).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.GalTrE

section KapSum

end KapSum

section KapB

end KapB

section Piece

variable {X X₁ : Scheme.{0}} [IsAffine X] [IsAffine X₁] [IsNoetherianRing Γ(X, ⊤)] [IsNoetherianRing Γ(X₁, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (h₁ : ∀ (m : Ideal Γ(X₁, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m)) {Λ : Type} [CommRing Λ]
  (f : X₁ ⟶ X) [Etale f]

/-- **Restriction to a piece of `X₁` factors through the piece of `X` below it.** -/
theorem resLE_piece (p₁ : minimalPrimes Γ(X₁, ⊤)) (q : minimalPrimes Γ(X, ⊤))
    (hq : (q : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁)) [Etale (Spec.map (CommRingCat.ofHom (kerLift hq)))]
    (c : H Λ (unitSh Λ X) 1) :
    resLE (piHom (piEquiv h₁) p₁) 1 (resLE f 1 c) =
      resLE (Spec.map (CommRingCat.ofHom (kerLift hq))) 1 (resLE (piHom (piEquiv h) q) 1 c) :=
  (resLE_comp _ _ c).symm.trans ((resLE_congr (piHom_comp_eq h h₁ f p₁ q hq) 1 c).trans (resLE_comp _ _ c))

end Piece

section GenPieces

universe u'

end GenPieces

section KapD

end KapD

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2j =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2j): stages S2-S3 on the charts

GLOB/REL PLAN v1, stages S2-S3 with `O = k[X]`, `O' = B₁` (via `φ₁`), `Y = Γ(Y₀)` (`Y₀` over `D_{g₀}`),
`G = Γ(W₁)` (`W₁` over `D₁ = chEt c φ₁`), `κ₀ = (prdMap d₀)^*`, `t = X - C a`:
* **`exists_S23B`**: `exists_S23` with the ring maps `φ`, `bW`, `aG`, `κ`, `aY` as parameters (so a chart instance
  is a plain application);
* **`exists_S23_chart`**: the chart instance. Its output feeds `exists_S4` (`hy`, `hz` with
  `Algebra B₁ (PiQ Γ(W₁)) := (toPiQ ∘ bW₁).toAlgebra`, `halg := fun _ => rfl`) and `isUnit_rho` (`y ∣ gamMap shG₀ c₀`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section S23B

variable {O O' Y G : Type} [CommRing O] [IsDomain O] [CommRing O'] [CommRing Y] [CommRing G] [Algebra O Y]
  (hY : ∀ (m : Ideal Y) [m.IsMaximal], IsDomain (Localization.AtPrime m)) [IsNoetherianRing Y]
  (hG : ∀ (m : Ideal G) [m.IsMaximal], IsDomain (Localization.AtPrime m)) [IsNoetherianRing G]
  [DecidableEq (minimalPrimes G)]

include hG in
/-- `exists_S23` with the ring maps as parameters. -/
theorem exists_S23B (φ : O →+* O') (bW : O' →+* G) (aG : O →+* G) (htow : ∀ c, bW (φ c) = aG c)
    (κ : Y →+* G) (aY : O →+* Y) (hAY : algebraMap O Y = aY) (hκ : ∀ c, κ (aY c) = aG c) (t : O)
    (hgenG : letI := bW.toAlgebra; ∀ x : G, x ∈ Algebra.adjoin O' (Set.range κ))
    {L L' : O} {e : ℕ} (hL : L = t ^ e * L') (hL' : IsUnit (φ L'))
    (hLY : ∀ y : Y, ∃ N : ℕ, IsIntegral O (L ^ N • y))
    (h1 : ∀ x : O', ∃ c : O, ∃ y : O', x = φ c + φ t * y)
    {ι : Type} [Finite ι] (J : ι → Ideal (integralClosure O Y)) (hJ : Pairwise fun i j => IsCoprime (J i) (J j))
    (hJt : ∀ (n : ℕ) (i : ι), IsCoprime (Ideal.span {algebraMap O (integralClosure O Y) t ^ n}) (J i))
    (htY : ∀ Q : minimalPrimes Y, toPiQ (aY t) Q ≠ 0)
    (hinj : ∀ q : minimalPrimes G, Function.Injective fun b : O' => toPiQ (bW b) q)
    (ht : ¬ IsUnit (φ t)) (htG : ∀ q : minimalPrimes G, toPiQ (aG t) q ≠ 0)
    (p₁ : minimalPrimes G) {u₁ : FractionRing (G ⧸ (p₁ : Ideal G))} (hu₁ : u₁ ≠ 0) {j : ℕ}
    (hj₁ : ∃ a, algebraMap (G ⧸ (p₁ : Ideal G)) _ a = toPiQ (aG t) p₁ ^ j * u₁)
    (hj₂ : ∃ b, algebraMap (G ⧸ (p₁ : Ideal G)) _ b = toPiQ (aG t) p₁ ^ j * u₁⁻¹) :
    ∃ (N : ℕ) (uS : integralClosure O Y) (z : PiQ G),
      (∀ i, uS - algebraMap O (integralClosure O Y) t ^ N ∈ J i) ∧
      (letI : Algebra O' (PiQ G) := (toPiQ.comp bW).toAlgebra; IsIntegral O' z) ∧
      liveMod hY (uS : Y) (aY t ^ N) ∈ Y⁰ ∧ (∃ c₀ : O, c₀ ≠ 0 ∧ liveMod hY (uS : Y) (aY t ^ N) ∣ aY c₀) ∧
      toPiQ (κ (liveMod hY (uS : Y) (aY t ^ N))) = toPiQ (aG t) ^ N * Function.update (1 : PiQ G) p₁ u₁ *
        (1 - toPiQ (aG t) * z) := by
  subst hAY
  let _ : Algebra O O' := φ.toAlgebra
  let _ : Algebra O' G := bW.toAlgebra
  let _ : Algebra O G := aG.toAlgebra
  have : IsScalarTower O O' G := IsScalarTower.of_algebraMap_eq fun c => (htow c).symm
  let κ₀ : Y →ₐ[O] G := { toRingHom := κ, commutes' := hκ }
  have htY' : ∀ Q : minimalPrimes Y, algebraMap O Y t ∉ (Q : Ideal Y) := by
    intro Q hQ
    apply htY Q
    rw [toPiQ_apply, Ideal.Quotient.eq_zero_iff_mem.2 hQ, map_zero]
  exact exists_S23 hY hG κ₀ t hgenG hL hL' hLY h1 J hJ hJt htY' hinj ht htG p₁ hu₁ hj₁ hj₂

end S23B

section S23Chart

end S23Chart

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP3a =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP3a): stages S2-S3 on the charts with `J` = the bad points

GLOB/REL PLAN v1: `exists_S23B` / `exists_S23_chart` (O2Gl2j) with `t = X - a` and `J_b = (X - b)` for the points
`b` with `p b` (`p b → b ≠ a`), so that no `J`-family has to be built at the chart level (instance paths on
`integralClosure k[X] Γ(Y₀)` built outside the generic lemma made the chart-level unification time out).
* helpers: `ne_zero_right_of_eq`, `dvd_map_of_eq`, `badJ`, `badJ_pairwise`, `badJ_coprime`, `badJ_mem`;
* **`exists_S23B_bad`** (generic rings) and **`exists_S23_chart_bad`** (the chart instance).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section PP3Helpers

section BadJ

end BadJ

end PP3Helpers

section S23BBad

variable {k : Type} [Field k] {O' Y G : Type} [CommRing O'] [CommRing Y] [CommRing G] [Algebra k[X] Y]
  (hY : ∀ (m : Ideal Y) [m.IsMaximal], IsDomain (Localization.AtPrime m)) [IsNoetherianRing Y]
  (hG : ∀ (m : Ideal G) [m.IsMaximal], IsDomain (Localization.AtPrime m)) [IsNoetherianRing G]
  [DecidableEq (minimalPrimes G)]

include hG in
/-- `exists_S23B` with `t = X - a` and `J` the bad points `(X - b)`, `p b`. -/
theorem exists_S23B_bad (φ : k[X] →+* O') (bW : O' →+* G) (aG : k[X] →+* G) (htow : ∀ c, bW (φ c) = aG c)
    (κ : Y →+* G) (aY : k[X] →+* Y) (hAY : algebraMap k[X] Y = aY) (hκ : ∀ c, κ (aY c) = aG c) (a : k)
    (hgenG : letI := bW.toAlgebra; ∀ x : G, x ∈ Algebra.adjoin O' (Set.range κ))
    {L L' : k[X]} {e : ℕ} (hL : L = (X - C a) ^ e * L') (hL' : IsUnit (φ L'))
    (hLY : ∀ y : Y, ∃ N : ℕ, IsIntegral k[X] (L ^ N • y))
    (h1 : ∀ x : O', ∃ c : k[X], ∃ y : O', x = φ c + φ (X - C a) * y)
    (p : k → Prop) [Finite (Subtype p)] (hpa : ∀ b, p b → b ≠ a)
    (htY : ∀ Q : minimalPrimes Y, toPiQ (aY (X - C a)) Q ≠ 0)
    (hinj : ∀ q : minimalPrimes G, Function.Injective fun b : O' => toPiQ (bW b) q)
    (ht : ¬ IsUnit (φ (X - C a))) (htG : ∀ q : minimalPrimes G, toPiQ (aG (X - C a)) q ≠ 0)
    (p₁ : minimalPrimes G) {u₁ : FractionRing (G ⧸ (p₁ : Ideal G))} (hu₁ : u₁ ≠ 0) {j : ℕ}
    (hj₁ : ∃ b, algebraMap (G ⧸ (p₁ : Ideal G)) _ b = toPiQ (aG (X - C a)) p₁ ^ j * u₁)
    (hj₂ : ∃ b, algebraMap (G ⧸ (p₁ : Ideal G)) _ b = toPiQ (aG (X - C a)) p₁ ^ j * u₁⁻¹) :
    ∃ (N : ℕ) (uS : integralClosure k[X] Y) (z : PiQ G),
      (∀ b, p b → uS - algebraMap k[X] (integralClosure k[X] Y) (X - C a) ^ N ∈
        Ideal.span {algebraMap k[X] (integralClosure k[X] Y) (X - C b)}) ∧
      (letI : Algebra O' (PiQ G) := (toPiQ.comp bW).toAlgebra; IsIntegral O' z) ∧
      liveMod hY (uS : Y) (aY (X - C a) ^ N) ∈ Y⁰ ∧ (∃ c₀ : k[X], c₀ ≠ 0 ∧ liveMod hY (uS : Y) (aY (X - C a) ^ N) ∣ aY c₀) ∧
      toPiQ (κ (liveMod hY (uS : Y) (aY (X - C a) ^ N))) = toPiQ (aG (X - C a)) ^ N * Function.update (1 : PiQ G) p₁ u₁ *
        (1 - toPiQ (aG (X - C a)) * z) :=
  (exists_S23B hY hG φ bW aG htow κ aY hAY hκ (X - C a) hgenG hL hL' hLY h1 (badJ p) (badJ_pairwise p)
    (badJ_coprime p hpa) htY hinj ht htG p₁ hu₁ hj₁ hj₂).imp fun _N h => h.imp fun _uS h => h.imp fun _z h =>
    ⟨fun b hb => badJ_mem hb (h.1 ⟨b, hb⟩), h.2⟩

end S23BBad

section S23Bad

end S23Bad

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gen1 =====
section

/-!
# S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`

* `ptCls_comp`: `PtCls c R x → PtCls c T (x ∘ Λ[r])`; `compSub r G` (`x ↦ x ∘ Λ[r]` pulled back subgroup).
* `isClosed_of_isLoc`: an `IsLoc` point is closed.
* chart facts for any open immersion `c : A¹ ⟶ P¹`: `chart_ne_genPt`, `chart_hclA`, `chart_hGal`, `chart_hclc`,
  `A1_hpt`, `exists_A1pt_of_mem_range`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtCompact.PushStk RamanujanPetersson.EtCompact.PushBC

section PtCompSub

end PtCompSub

section CompSub

variable {Λ : Type} [CommRing Λ] {P : Scheme.{0}}

/-- An `IsLoc` point is closed. -/
theorem isClosed_of_isLoc {F : EtSh Λ P} {z : P} {β : Ext.{0} (freeSh Λ (etId P)) F 2} (hβ : IsLoc Λ F z β) :
    IsClosed ({z} : Set P) := by
  obtain ⟨Uo, Uz, h, hz, -⟩ := hβ
  have he : ({z} : Set P) = (Uz : Set P)ᶜ := by
    ext x
    rw [Set.mem_singleton_iff, Set.mem_compl_iff, SetLike.mem_coe, hz x, not_not]
  rw [he]
  exact Uz.isOpen.isClosed_compl

end CompSub

section Chart

end Chart

end RamanujanPetersson.EtPBC.EtMV

end

end


