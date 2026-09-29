-- Prove2me | Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
-- name    : AlgebraicGeometry_OModulePresheafLerayDoubleComplex
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/0e048868-e76d-55dd-a656-38d5aba2e967
-- title:
--   The Čech–Leray double complex of a morphism
-- statement:
--   Fix a commutative ring $R$, a morphism $\pi_Z\colon Z\to\operatorname{Spec}R$, a morphism $p\colon V'\to Z$, and finite ordered affine open covers $K$ of $Z$ and $K'$ of $V'$ (indexed by finite linearly ordered types, so that chains $\sigma$ of length $a+1$ are strictly monotone index tuples and $K.\mathrm{inter}\,\sigma$ is the intersection of the corresponding members). The main definition is `LerayDblCpx p πZ K K'`, an element of the project's [`DoubleComplex.Bounded R`](../def/AlgebraicGeometry_DoubleComplex.html#L11): a first-quadrant array of $R$-modules with horizontal and vertical differentials satisfying $d_H^2=0$, $d_V^2=0$ and $d_V d_H=d_H d_V$ as structure fields, together with an integer $N$ and a proof that the terms are subsingletons outside the range $a,b<N$. Its terms are $\mathrm{biC}$, the products over pairs $(\sigma,\tau)$ of $\Gamma(V', U'_\tau\cap p^{-1}U_\sigma)$; the differentials are the alternating Čech differentials $\mathrm{dH}$ in $\sigma$ and $\mathrm{dV}$ in $\tau$; and $N=\max(|K.\iota|,|K'.\iota|)$. The three commutation identities are supplied by `dH_sq`, `dV_sq` and `dHV_comm`, the first two being reduced to the general vanishing `d_d` of the square of the Čech differential of a presheaf of modules, itself resting on the cosimplicial identity `succAbove_comp_succAbove` for the face maps on strictly monotone tuples. Four further projections record the terms, the bound and the two differentials.
--
--   The module also defines two augmentations: `biAug`, from the Čech cochains of $K'$ in degree $b$ with values in the structure sheaf to the column $\mathrm{biC}\,0\,b$, given on each pair by restriction along $U'_\tau\cap p^{-1}U_\sigma\le U'_\tau$; and `relAug`, from $\Gamma(V', p^{-1}U)$ to the degree-zero part of the relative alternating complex over an open $U\subseteq Z$, again by restriction. Assuming $\pi_Z$ and $p\circ\pi_Z$ separated, `rowCoverOf p πZ K K' τ` is the ordered affine cover of $U'_\tau$ by the opens $U'_\tau\cap p^{-1}U_i$, affine by the stability of affineness under such fibre products; `inter_rowCoverOf` identifies its $a$-fold intersections with the terms $U'_\tau\cap p^{-1}U_\sigma$ of the double complex, and `inter_restrictToPreimage` does the same for the cover of $p^{-1}U$ obtained from $K'$. Auxiliary lemmas `map_iInf_fin` (preimages commute with finite infima of opens) and `res_at_eq` (restrictions agree along equal chains) support these identifications.
--
--   **Relation to Mathlib.** Mathlib has no Čech–Leray double complex for a morphism of schemes in this form; the complex is built on the project's own `OModulePresheaf`, `Scheme.OrderedAffineCover(Of)` and [`DoubleComplex.Bounded`](../def/AlgebraicGeometry_DoubleComplex.html#L11), with terms given by products of sections of the structure sheaf rather than by Mathlib's homological algebra API.
--
--   **Where it is used.** The complex and its augmentations feed the Leray-type spectral sequence comparing Čech cohomology on $V'$ with Čech cohomology on $Z$ of the pushforward, used in the cohomological input to the modularity argument (finiteness and base-change properties of coherent cohomology).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf
import Definitions.Def_AlgebraicGeometry_DoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.OModulePresheaf.Leray

theorem succAbove_comp_succAbove {n : ℕ} {i j : Fin (n + 2)} (H : i ≤ j) :
    Fin.succAbove j.succ ∘ Fin.succAbove i = Fin.succAbove i.castSucc ∘ Fin.succAbove j := by
  ext k
  simp only [Function.comp_apply, Fin.succAbove]
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩; rcases k with ⟨k, hk⟩
  simp only [Fin.le_def] at H
  simp only [Fin.lt_def, Fin.castSucc_mk, Fin.succ_mk, Fin.val_castSucc]
  split_ifs <;> simp_all only [Fin.val_succ, Fin.val_castSucc] <;> omega

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

theorem res_at_eq {i : ℕ} {t t' : K.Idx i} (heq : t = t') (f : F.cochain K i) {U : V.Opens}
    (h : U ≤ K.inter t) (h' : U ≤ K.inter t') : F.res h (f t) = F.res h' (f t') := by
  subst heq; rfl

theorem d_d (i : ℕ) : F.d K (i + 1) ∘ₗ F.d K i = 0 := by
  refine LinearMap.ext fun f => funext fun s => ?_
  rw [LinearMap.comp_apply, OModulePresheaf.d_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [OModulePresheaf.d_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul, ← pow_add]

  have hres : ∀ (a : Fin (i + 3)) (b : Fin (i + 2)),
      F.res (K.inter_le_inter_face s a)
          (F.res (K.inter_le_inter_face (K.face s a) b) (f (K.face (K.face s a) b)))
        = F.res ((K.inter_le_inter_face s a).trans (K.inter_le_inter_face (K.face s a) b))
            (f (K.face (K.face s a) b)) :=
    fun a b => (congrFun (congrArg DFunLike.coe (F.res_comp _ _)) _).symm
  simp only [hres]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  set S : Finset (Fin (i + 3) × Fin (i + 2)) := {ab | (ab.1 : ℕ) ≤ (ab.2 : ℕ)}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij
    (fun ab (hab : ab ∈ S) =>
      (ab.2.succ, Fin.castLT ab.1
        (Nat.lt_of_le_of_lt (Finset.mem_filter.mp hab).2 ab.2.isLt)))
    ?hmem ?hinj ?hsurj ?hterm
  case hmem =>
    rintro ⟨a, b⟩ hab
    simp only [S, Finset.compl_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_succ, not_le, Fin.val_castLT]
    exact Nat.lt_succ_of_le (Finset.mem_filter.mp hab).2
  case hinj =>
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    have h2 := congrArg Prod.snd heq
    exact Prod.ext (Fin.eq_of_val_eq (by simpa using congrArg Fin.val h2))
      (Fin.succ_injective _ (congrArg Prod.fst heq))
  case hsurj =>
    rintro ⟨a', b'⟩ hab'
    have hlt : (b' : ℕ) < (a' : ℕ) := by
      simpa [S, Finset.compl_filter, Finset.mem_filter, not_le] using hab'
    have ha'0 : a' ≠ 0 := fun h => by simp [h] at hlt
    refine ⟨(Fin.castSucc b', a'.pred ha'0), ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
        Fin.val_pred]; omega
    · exact Prod.ext (Fin.succ_pred a' ha'0)
        (Fin.eq_of_val_eq (by simp only [Fin.val_castLT, Fin.val_castSucc]))
  case hterm =>
    rintro ⟨a, b⟩ hab
    have hba : (a : ℕ) ≤ (b : ℕ) := (Finset.mem_filter.mp hab).2
    set a' : Fin (i + 2) := Fin.castLT a (Nat.lt_of_le_of_lt hba b.isLt)
    have halt : a' ≤ b := Fin.le_def.mpr (by simpa [a'] using hba)
    have hacs : a'.castSucc = a := Fin.eq_of_val_eq (by simp [a'])
    have hface : K.face (K.face s a) b = K.face (K.face s b.succ) a' := by
      apply Subtype.ext
      change s.1 ∘ (Fin.succAbove a ∘ Fin.succAbove b) = s.1 ∘ (Fin.succAbove b.succ ∘ Fin.succAbove a')
      rw [← hacs, succAbove_comp_succAbove halt]
    have hsign : ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ)))
        = -((-1 : ℤ) ^ (((b.succ : Fin (i + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show ((b : ℕ) + 1 + (a : ℕ)) = ((a : ℕ) + (b : ℕ)) + 1 from by ring, pow_succ]; ring
    rw [hsign, neg_smul]
    refine congrArg Neg.neg (congrArg₂ (· • ·) (by congr 1) ?_)
    exact res_at_eq F K hface f _ _

theorem d_d_apply (i : ℕ) (c : F.cochain K i) : F.d K (i + 1) (F.d K i c) = 0 :=
  congrFun (congrArg DFunLike.coe (d_d F K i)) c

theorem map_iInf_fin {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ} (U : Fin (n + 1) → Y.Opens) :
    (TopologicalSpace.Opens.map f.base).obj (⨅ j, U j) = ⨅ j, (TopologicalSpace.Opens.map f.base).obj (U j) := by
  have hsplit : ∀ {α : Type u} [CompleteLattice α] {m : ℕ} (g : Fin (m + 2) → α),
      (⨅ j : Fin (m + 2), g j) = g 0 ⊓ (⨅ j : Fin (m + 1), g j.succ) := fun g =>
    le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
      (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
  induction n with
  | zero => simp only [show (⨅ j : Fin 1, U j) = U 0 from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl),
      show (⨅ j : Fin 1, (TopologicalSpace.Opens.map f.base).obj (U j)) = (TopologicalSpace.Opens.map f.base).obj (U 0) from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)]
  | succ m ih =>
    rw [hsplit U, show (TopologicalSpace.Opens.map f.base).obj (U 0 ⊓ (⨅ j : Fin (m + 1), U j.succ))
        = (TopologicalSpace.Opens.map f.base).obj (U 0) ⊓ (TopologicalSpace.Opens.map f.base).obj (⨅ j : Fin (m + 1), U j.succ)
      from rfl, ih (fun j => U j.succ), hsplit (fun j => (TopologicalSpace.Opens.map f.base).obj (U j))]

section DblCpx

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

theorem dV_sq (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    dV p πZ K K' a (b + 1) ∘ₗ dV p πZ K K' a b = 0 := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine LinearMap.ext fun x => (biC_uncurry p πZ K K' a (b + 2)).injective (funext fun σ => ?_)
  have h₁ := dV_uncurry p πZ K K' a (b + 1) (dV p πZ K K' a b x) σ
  rw [dV_uncurry p πZ K K' a b x σ, relAltd_eq_d, relAltd_eq_d] at h₁
  exact (h₁.trans (d_d_apply (pushOpen p πZ (K.inter σ)) K' b _)).trans
    (congrFun (map_zero (biC_uncurry p πZ K K' a (b + 2))) σ).symm

theorem dH_sq (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    dH p πZ K K' (a + 1) b ∘ₗ dH p πZ K K' a b = 0 := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine LinearMap.ext fun x => (biC_uncurry' p πZ K K' (a + 2) b).injective (funext fun τ => ?_)
  have h₁ := dH_uncurry p πZ K K' (a + 1) b (dH p πZ K K' a b x) τ
  rw [dH_uncurry p πZ K K' a b x τ] at h₁
  exact (h₁.trans (d_d_apply (pullOpen p πZ (K'.inter τ)) K a _)).trans
    (congrFun (map_zero (biC_uncurry' p πZ K K' (a + 2) b)) τ).symm

theorem dHV_comm (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    dV p πZ K K' (a + 1) b ∘ₗ dH p πZ K K' a b = dH p πZ K K' a (b + 1) ∘ₗ dV p πZ K K' a b := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine LinearMap.ext fun x => funext fun στ => ?_
  simp only [LinearMap.comp_apply, dH_apply', dV_apply', map_sum, map_zsmul, Finset.smul_sum, smul_smul,
    Scheme.TwoAffineOpenCover.res_res]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

def LerayDblCpx : DoubleComplex.Bounded R :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  { C := biC p πZ K K'
    dH := dH p πZ K K'
    dV := dV p πZ K K'
    dH_sq := dH_sq p πZ K K'
    dV_sq := dV_sq p πZ K K'
    dHV_comm := dHV_comm p πZ K K'
    N := max (Fintype.card K.ι) (Fintype.card K'.ι)
    hBound := biC_subsingleton p πZ K K' }

theorem LerayDblCpx_C (a b : ℕ) : (LerayDblCpx p πZ K K').C a b = biC p πZ K K' a b := rfl
theorem LerayDblCpx_N : (LerayDblCpx p πZ K K').N = max (Fintype.card K.ι) (Fintype.card K'.ι) := rfl
theorem LerayDblCpx_dH (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (LerayDblCpx p πZ K K').dH a b = dH p πZ K K' a b := rfl
theorem LerayDblCpx_dV (a b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (LerayDblCpx p πZ K K').dV a b = dV p πZ K K' a b := rfl

def biAug (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (OModulePresheaf.unit (p ≫ πZ)).cochain K' b →ₗ[R] biC p πZ K K' 0 b :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.pi fun στ => Scheme.OrderedAffineCoverOf.res (p ≫ πZ) inf_le_left ∘ₗ LinearMap.proj στ.2

theorem biAug_apply (b : ℕ) (y : (OModulePresheaf.unit (p ≫ πZ)).cochain K' b) (στ : BiIdx K K' 0 b) :
    biAug p πZ K K' b y στ
      = (V'.presheaf.map (homOfLE (inf_le_left : biOpen p K K' 0 b στ.1 στ.2 ≤ K'.inter στ.2)).op).hom (y στ.2) :=
  rfl

end DblCpx

section RelAug

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) (K' : Scheme.OrderedAffineCover V') (U : Z.Opens)

def relAug :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (pullOpen p πZ (⊤ : V'.Opens)).obj U →ₗ[R] relAltC p πZ K' U 0 :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearMap.pi fun _ => Scheme.OrderedAffineCoverOf.res (p ≫ πZ) (inf_le_inf_right _ le_top)

theorem relAug_apply (w : (pullOpen p πZ (⊤ : V'.Opens)).obj U) (τ : K'.Idx 0) :
    relAug p πZ K' U w τ
      = (V'.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj U)
          (le_top : K'.inter τ ≤ ⊤))).op).hom w :=
  rfl

end RelAug

section RowCover

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated πZ] [IsSeparated (p ≫ πZ)]
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

def rowCoverOf {q : ℕ} (τ : K'.Idx q) : V'.OrderedAffineCoverOf (K'.inter τ) where
  ι := K.ι
  U i := K'.inter τ ⊓ (Opens.map p.base).obj (K.U i)
  isAffineOpen i := Scheme.OrderedAffineCover.fiberAffineOpen p πZ
    (Scheme.OrderedAffineCover.isAffineOpen_inter (p ≫ πZ) K' τ) (K.isAffineOpen i)
  le _ := inf_le_left
  iSup_eq := le_antisymm (iSup_le fun _ => inf_le_left) fun x hx =>
    let ⟨i, hi⟩ := Opens.mem_iSup.mp (show p.base x ∈ ⨆ i, K.U i from K.iSup_eq_top.symm ▸ trivial)
    Opens.mem_iSup.mpr ⟨i, hx, hi⟩

theorem rowCoverOf_U {q : ℕ} (τ : K'.Idx q) (i : K.ι) :
    (rowCoverOf p πZ K K' τ).U i = K'.inter τ ⊓ (Opens.map p.base).obj (K.U i) := rfl

theorem inter_rowCoverOf {a b : ℕ} (τ : K'.Idx b) (σ : (rowCoverOf p πZ K K' τ).Idx a) :
    (rowCoverOf p πZ K K' τ).inter σ = biOpen p K K' a b σ τ := by
  show (⨅ j, K'.inter τ ⊓ (Opens.map p.base).obj (K.U (σ.1 j)))
    = K'.inter τ ⊓ (Opens.map p.base).obj (⨅ j, K.U (σ.1 j))
  rw [map_iInf_fin p (fun j => K.U (σ.1 j)), ← inf_iInf]

end RowCover

section RestrictToPreimage

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated πZ] (K' : Scheme.OrderedAffineCover V')

theorem inter_restrictToPreimage {U : Z.Opens} (hU : IsAffineOpen U) {b : ℕ}
    (τ : (restrictToPreimage p πZ K' hU).Idx b) :
    (restrictToPreimage p πZ K' hU).inter τ = K'.inter τ ⊓ (Opens.map p.base).obj U := by
  show (⨅ j, K'.U (τ.1 j) ⊓ (Opens.map p.base).obj U) = (⨅ j, K'.U (τ.1 j)) ⊓ (Opens.map p.base).obj U
  exact le_antisymm (le_inf (iInf_mono fun _ => inf_le_left) ((iInf_le _ 0).trans inf_le_right))
    (le_iInf fun j => inf_le_inf_right _ (iInf_le _ j))

end RestrictToPreimage

end AlgebraicGeometry.OModulePresheaf.Leray

end


