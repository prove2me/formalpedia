-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_079
-- name    : RPLib_FX_EtPBC_079
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:42:00.8099+00:00
-- url     : https://prove2.me/theorems/48627504-7b52-5364-a8fb-17d11838ca86
-- title:
--   Proper base change for the projective line, library file 079
-- statement:
--   File 079 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Gl3a`: S4-EtPBC-A, O2 GLOB (O2Gl3a): chart facts for the `uk_diff` call on `D₂`
--   * `S4.Def_RP_EtPBC_A_O2Bd4`: S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`
--   * `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
--   * `S4.Def_RP_EtPBC_A_O2L6b3`: S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`
--   * `S4.Def_RP_EtPBC_A_O2L7b1`: S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_071

/-!
# Proper base change for the projective line, library file 079

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Gl3a`: S4-EtPBC-A, O2 GLOB (O2Gl3a): chart facts for the `uk_diff` call on `D₂`
* `S4.Def_RP_EtPBC_A_O2Bd4`: S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`
* `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
* `S4.Def_RP_EtPBC_A_O2L6b3`: S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`
* `S4.Def_RP_EtPBC_A_O2L7b1`: S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2Gl3a =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl3a): chart facts for the `uk_diff` call on `D₂`

* **`not_mem_fpt_of_eval_ne_zero`**: `g(a) ≠ 0` ⇒ `φ g` is not in the prime of a fibre point over `c(a)`
  (so `D₂ := (D₁)_{φ₁ c₀'}` keeps the point over `z`: `nonempty_fib_toDF`);
* **`wm_mG_sXW`**: `m^*` carries the root of unity `sXW` on `Y_G` to the one on `W₂` (`hs` of `uk_diff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Cech

section Pts3

end Pts3

section SXW

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {g₀ G : k[X]} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  {B₂ : CommRingCat.{0}} (φ₂ : CommRingCat.of k[X] ⟶ B₂) [Etale (Spec.map φ₂ ≫ c)]
  [IsAffine (prd (chEt c φ₂) (opEt Uo)).left]
  (hD₂ : ∀ v : (prd (chEt c φ₂) (opEt Uo)).left, (prd (chEt c φ₂) (opEt Uo)).hom v ∈ opnDg c G)
  (d : chEt c φ₂ ⟶ chEt c (locF (B := CommRingCat.of k[X]) g₀))

include hG₀ d in
/-- `m^*` carries `sXW` on `Y_G` to `sXW` on `W₂` (`hs` of `uk_diff` with `T' = prd D_G U₀`). -/
theorem wm_mG_sXW (ζ0 : k) :
    (wm (R := R) (mG c hle (chEt c φ₂) hD₂)).appTop (sXW c (locF (B := CommRingCat.of k[X]) G) (Uo := Uo) R ζ0) =
      sXW c φ₂ (Uo := Uo) R ζ0 :=
  (congrArg (fun x => (wm (R := R) (mG c hle (chEt c φ₂) hD₂)).appTop x)
      (wm_appTop_sXW c (locF (B := CommRingCat.of k[X]) g₀) (locF (B := CommRingCat.of k[X]) G) (Uo := Uo) R
        (toDG c hG₀) ζ0).symm).trans
    ((wm_mG_appTop c R hG₀ hle φ₂ hD₂ d _).trans
      (wm_appTop_sXW c (locF (B := CommRingCat.of k[X]) g₀) φ₂ (Uo := Uo) R d ζ0))

end SXW

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Bd4 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`

s128 fix of REL PLAN v2: a bad point `c(b)` has `g₀(b) = 0` (`c(D(g₀)) ⊆ U₀ ∪ {z}`), so no chart `D' ∋ b` maps to
`D_{g₀}`. The map `W(D') → Y₀` is `m^* ∘ ρ` instead (`m := mG : D' ×_P U₀ ⟶ D_G ×_P U₀`, `ρ := (prdMap (toDG c hG₀))^*`):
* **`wD_hom`**, **`shG_wm_any`**: `wm m ≫ shG φ₁ = shG φ₂` for ANY `m : D₂ ×_P U₀ ⟶ D₁ ×_P U₀` between chart products;
* **`mG_rho_gamMap`**, **`mG_H_any`**: `m^* (ρ r) = bW'(φ' r)`; the `H`-relation pulled back along `m`;
* **`exists_bad_e'`**: `exists_bad_e` (O2Bd2) without `d : D' ⟶ D_{g₀}`;
* **`exists_S4H'`**: `exists_S4H` (O2Gl2k) for a generic `G` (`hG₀ : g₀ ∣ G`), also returning `H ρ(t)^N = ρ(y)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section WDHom

end WDHom

section AnyM

end AnyM

section BadChart'

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {g₀ G : k[X]} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  {B' : CommRingCat.{0}} (φ' : CommRingCat.of k[X] ⟶ B') [Etale (Spec.map φ' ≫ c)]
  [IsAffine (prd (chEt c φ') (opEt Uo)).left]
  (hD' : ∀ v : (prd (chEt c φ') (opEt Uo)).left, (prd (chEt c φ') (opEt Uo)).hom v ∈ opnDg c G)

/-- The `H`-relation on `Y_G` pulled back along `m`. -/
theorem mG_H_any (r : k[X]) (N : ℕ)
    {y : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)}
    {H : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)}
    (hH : H * (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop
      (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) r) ^ N =
      (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop y) :
    (wm (R := R) (mG c hle (chEt c φ') hD')).appTop H * (bW (Spec.map φ' ≫ c) (opEt Uo) R).hom (φ'.hom r) ^ N =
      (wm (R := R) (mG c hle (chEt c φ') hD')).appTop ((wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop y) := by
  rw [← mG_rho_gamMap c R hG₀ hle φ' hD' r, ← map_pow, ← map_mul, hH]

end BadChart'

section S4H'

end S4H'

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6b2 =====
section

/-!
# S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`

For a chart `D = chEt c φ` (`B` Dedekind, `(X - a)` a nonzero prime) and `s' : D ⟶ ιP^* W`:
* the point `d₀ = (X - a)` of `D` over `z = c a` and its `K`-point `δ₀` (`δ₀_hom : δ₀ ≫ D.hom = ptz`);
* `wK = s'(d₀)`, the `K`-point `v'` of `Vs` over `sK` (`v'_hom`), `gE₀ : D ⟶ Es` (`v ↦ (s' v, σ₀ v)`);
* `Vb = gE₀⁻¹(Og)`, `Db = opn D Vb` (`d₀ ∈ Vb`), its fibre at `z` (subsingleton, nonempty) and `hSb`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum

section Sq

end Sq

section Pt

end Pt

section Fib

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)] [IsDedekindDomain B]
  (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime)
  (s' : chEt c φ ⟶ (etPull (ιP gS s)).obj W)

/-- `gE₀ : D ⟶ Es`, `v ↦ (s' v, σ₁ v)`. -/
def gE₀ : (chEt c φ).left ⟶ (Es (σz K gS (zc c a) (chart_hclA c a)) (qV K gS) W).left :=
  pullback.lift (s'.left ≫ pullback.fst W.hom (ιP gS s)) ((chEt c φ).hom ≫ σ₁ gS s c a W φ ht hP s')
    ((pullPt_sq (ιP gS s) W s').trans ((Category.assoc _ _ _).trans
      (whisker_eq _ (σ₀_snd gS s c a W _ (v'_hom gS s c a W φ ht hP s')))).symm)

theorem gE₀_fst : gE₀ gS s c a W φ ht hP s' ≫ pullback.fst W.hom
    (Zs (σz K gS (zc c a) (chart_hclA c a)) (qV K gS) W).hom = s'.left ≫ pullback.fst W.hom (ιP gS s) :=
  pullback.lift_fst _ _ _

/-- `ptz ≫ σ₁ = v' ≫ jz`. -/
theorem ptz_σ₁ : ptz K (zc c a) (chart_hclA c a) ≫ σ₁ gS s c a W φ ht hP s' =
    v' gS s c a W φ ht hP s' ≫ jz W (σz_qV K gS (zc c a) (chart_hclA c a)) := by
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ((whisker_eq _ (σ₀_fst gS s c a W _ _)).trans ?_)
    refine ((Category.assoc _ _ _).symm.trans ((eq_whisker (ptz_toSpecK K _ _) _).trans
      (Category.id_comp _))).trans ?_
    exact ((Category.comp_id _).symm.trans (whisker_eq _ (jz_fst W _).symm)).trans (Category.assoc _ _ _).symm
  · refine (Category.assoc _ _ _).trans ((whisker_eq _ (σ₀_snd gS s c a W _ _)).trans ?_)
    refine (ptz_ιP gS s (zc c a) (chart_hclA c a)).trans ?_
    exact ((eq_whisker (v'_hom gS s c a W φ ht hP s') _).symm.trans (Category.assoc _ _ _)).trans
      ((whisker_eq _ (jz_snd W _).symm).trans (Category.assoc _ _ _).symm)

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6b3 =====
section

/-!
# S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`

`a' : D♭ ×_P Uz' ⟶ ιP^* DzO`, `a : D♭ ⟶ ιP^* Dz`, `b : Uz' ⟶ ιP^*(Zz ×_P Uz)`, `c := σP`, with the four squares
`h₁ .. h₄` (all proved on underlying scheme maps through `toPull`), and **`mvTheta_Db`**:
`Λ[σP] ∘ (ιP^*MVZ-class of κ, r) = (locC D♭-class of a'^*κ, a ≫ r)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

section Mor

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)] [IsDedekindDomain B]
  (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime)
  (s' : chEt c φ ⟶ (etPull (ιP gS s)).obj W)
  (Uz' : (P1 K).Opens) (hUz' : ∀ x : P1 K, x ∈ Uz' ↔ x ≠ zc c a)

theorem hB0 : (Uz'.ι ≫ σ₁ gS s c a W φ ht hP s') ≫ (Zz K gS (zc c a) (chart_hclA c a) W).hom =
    ιU gS s c a Uz' hUz' ≫ (opEt (Uz K gS (zc c a) (chart_hclA c a))).hom :=
  ((Category.assoc _ _ _).trans (whisker_eq _ (σ₀_snd gS s c a W _ (v'_hom gS s c a W φ ht hP s')))).trans
    ((ιU_eq gS s c a Uz' hUz').trans ((Category.assoc _ _ _).trans (whisker_eq _ (Category.id_comp _)))).symm

end Mor

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7b1 =====
section

/-!
# S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
For a `K`-rational geometric point `s` (`[IsIso (s.pt ≫ gS)]`), `e := fibToP1 : P_s ⟶ P¹_K` is an isomorphism with
`e ≫ ιP = ι` (`fibToP1_ιP`). Base change identifications `isoE X : e^*ιP^*X ⟶ ι^*X` (natural, invertible),
the section `σG` of `ιP^*(qV^*V)` through a `K`-point `v'` of `V`, the neighbourhood `jG = (V, v')` of `s`, and
**`nbhdSec_eq`**: `nbhdSec jG = c₀ ≫ e^*σG ≫ isoE`. **`TrE`**: `Ext²(Λ[P¹], Λ[ιP^*R]) → Ext²(Λ_{P_s}, ι^*Λ[R])`,
`x ↦ u ∘ e^*x ∘ v`; **`TrE_surjective`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

universe u

section Gen

end Gen

section GenSurj

universe w v₁ u₁ v₂ u₂

end GenSurj

section Fib

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)]

variable (Λ : Type) [CommRing Λ]

/-- **The transport** `Ext²(Λ[P¹_K], Λ[ιP^*R]) → Ext²(Λ_{P_s}, ι^*Λ[R])`, `x ↦ u ∘ e^*x ∘ v`. -/
def TrE (R : (PV K gS).Etale) (x : Ext.{0} (freeSh Λ (etId (P1 K))) (freeSh Λ ((etPull (ιP gS s)).obj R)) 2) :
    Ext.{0} (unitSh Λ (fib (qV K gS) s)) ((pull (fibι (qV K gS) s) Λ).obj (freeSh Λ R)) 2 :=
  (Ext.mk₀ (uE gS s Λ)).comp ((x.mapExactFunctor (pull (fibToP1 K gS s) Λ)).comp (Ext.mk₀ (vE gS s Λ R))
    (add_zero 2)) (zero_add 2)

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end


