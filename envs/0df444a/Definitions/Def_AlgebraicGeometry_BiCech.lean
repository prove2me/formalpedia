-- Prove2me | Definitions.Def_AlgebraicGeometry_BiCech
-- name    : AlgebraicGeometry_BiCech
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/e46caa46-1385-5285-98e2-848dfdb23448
-- title:
--   Ordered open families and their bi-Čech double complex
-- statement:
--   For a scheme $Z$, `Scheme.OrderedOpenFamily` is a family $U\colon \iota\to Z.\mathrm{Opens}$ indexed by a finite linearly ordered type $\iota$, with no affineness and no covering condition imposed. As for the project's `Scheme.OrderedAffineCover`, one sets $\mathrm{Idx}\,p$ to be the strictly monotone maps $\mathrm{Fin}(p+1)\to\iota$ (a finite type), $\mathrm{inter}\,s=\bigsqcap_j U(s_j)$, and $\mathrm{face}\,s\,j$ to be $s$ precomposed with `Fin.succAbove j`, i.e. the chain with its $j$-th entry deleted; the accompanying lemmas give $\mathrm{inter}\,s\le U(s_j)$, $\mathrm{inter}\,s\le\mathrm{inter}(\mathrm{face}\,s\,j)$, and the emptiness of $\mathrm{Idx}\,p$ once $\#\iota\le p$. Two further constructions: `prodCover` takes families $\mathfrak A,\mathfrak B$ together with hypotheses that each $\mathfrak A.U\,i\sqcap\mathfrak B.U\,j$ is affine open and that these meets have supremum $\top$, and returns the ordered affine cover indexed by the lexicographic product $\mathfrak A.\iota\times_{\mathrm{lex}}\mathfrak B.\iota$ with opens the pairwise meets; `toOpenFamily` forgets the affineness and covering fields of an ordered affine cover, and `imageFamily` sends an ordered affine cover $K$ of $W$ and an open immersion $f\colon W\to Z$ to the family $i\mapsto f\,''^{\mathrm U}\,K.U\,i$ of opens of $Z$.
--
--   Given $\pi\colon Z\to\operatorname{Spec} R$, an `OModulePresheaf` $F$ over $\pi$ (sections on opens, $R$-linear restrictions compatible with the structure sheaf) and two ordered open families $\mathfrak A,\mathfrak B$, the bi-Čech groups are $C\,p\,q=\prod_{(s,t)}F(\mathrm{inter}\,s\sqcap\mathrm{inter}\,t)$ over $s\in\mathfrak A.\mathrm{Idx}\,p$, $t\in\mathfrak B.\mathrm{Idx}\,q$. The $R$-linear maps `dH` and `dV` have components $\sum_{j}(-1)^{j}\,\mathrm{res}$ applied to the $(\mathrm{face}\,s\,j,t)$, respectively $(s,\mathrm{face}\,t\,j)$, entries; `dH_apply` and `dV_apply` record these component formulas. The theorems `dH_sq`, `dV_sq` assert that the successive horizontal, respectively vertical, composites vanish, and `dHV_comm` that $dV\circ dH=dH\circ dV$ (commuting, not anticommuting). Helper results `succAbove_comp_succAbove` (the simplicial identity for face insertions) and `res_left_eq`, `res_right_eq` (transport of restricted sections along an equality of indices) are used for these. Finally `biCech` assembles this data into a [`DoubleComplex.Bounded R`](../def/AlgebraicGeometry_DoubleComplex.html#L11), with bound field $N=\max(\#\mathfrak A.\iota,\#\mathfrak B.\iota)$ and the boundedness requirement verified from the emptiness of high-degree index sets; `biCech_C`, `biCech_dH`, `biCech_dV`, `biCech_N` identify its fields.
--
--   **Relation to Mathlib.** Mathlib has open covers of schemes and Čech nerves, but not the alternating Čech complex of a linearly ordered finite family, nor the bounded double complex of $R$-modules used here; `Scheme.OrderedOpenFamily` and the bi-Čech construction are the project's own, the former being the project's `Scheme.OrderedAffineCover` with the affineness and covering fields dropped.
--
--   **Where it is used.** This vocabulary serves the comparison of alternating Čech complexes for different covers — Mayer–Vietoris and product-cover (Eilenberg–Zilber) arguments via the total complex and spectral sequence of a bounded double complex — in the treatment of coherent cohomology used in the modularity part of the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_BiCech.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_DoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

structure Scheme.OrderedOpenFamily (Z : Scheme.{u}) where

  ι : Type u
  [instFintype : Fintype ι]
  [instLinearOrder : LinearOrder ι]

  U : ι → Z.Opens

attribute [instance] Scheme.OrderedOpenFamily.instFintype Scheme.OrderedOpenFamily.instLinearOrder

namespace Scheme.OrderedOpenFamily

variable {Z : Scheme.{u}} (𝔄 : Z.OrderedOpenFamily)

def Idx (p : ℕ) : Type u := {s : Fin (p + 1) → 𝔄.ι // StrictMono s}

instance instFintypeIdx (p : ℕ) : Fintype (𝔄.Idx p) := Subtype.fintype _

instance instDecidableEqIdx (p : ℕ) : DecidableEq (𝔄.Idx p) := Classical.decEq _

def inter {p : ℕ} (s : 𝔄.Idx p) : Z.Opens := ⨅ j, 𝔄.U (s.1 j)

def face {p : ℕ} (s : 𝔄.Idx (p + 1)) (j : Fin (p + 2)) : 𝔄.Idx p :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

theorem face_val {p : ℕ} (s : 𝔄.Idx (p + 1)) (j : Fin (p + 2)) : (𝔄.face s j).1 = s.1 ∘ Fin.succAbove j := rfl

theorem inter_le {p : ℕ} (s : 𝔄.Idx p) (j : Fin (p + 1)) : 𝔄.inter s ≤ 𝔄.U (s.1 j) := iInf_le _ j

theorem inter_le_inter_face {p : ℕ} (s : 𝔄.Idx (p + 1)) (j : Fin (p + 2)) :
    𝔄.inter s ≤ 𝔄.inter (𝔄.face s j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

theorem isEmpty_idx_of_card_le {p : ℕ} (h : Fintype.card 𝔄.ι ≤ p) : IsEmpty (𝔄.Idx p) := by
  refine ⟨fun s => ?_⟩
  have := Fintype.card_le_of_injective s.1 s.2.injective
  simp only [Fintype.card_fin] at this
  omega

def prodCover (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))
    (hcov : ⨆ ij : 𝔄.ι × 𝔅.ι, 𝔄.U ij.1 ⊓ 𝔅.U ij.2 = ⊤) : Z.OrderedAffineCover where
  ι := 𝔄.ι ×ₗ 𝔅.ι
  instFintype := inferInstanceAs (Fintype (𝔄.ι × 𝔅.ι))
  instLinearOrder := inferInstance
  U ij := 𝔄.U (ofLex ij).1 ⊓ 𝔅.U (ofLex ij).2
  isAffineOpen ij := haff _ _
  iSup_eq_top := by
    rw [← hcov]
    exact le_antisymm (iSup_le fun ij => le_iSup (fun ij : 𝔄.ι × 𝔅.ι => 𝔄.U ij.1 ⊓ 𝔅.U ij.2) (ofLex ij))
      (iSup_le fun ij => le_iSup (fun ij : 𝔄.ι ×ₗ 𝔅.ι => 𝔄.U (ofLex ij).1 ⊓ 𝔅.U (ofLex ij).2) (toLex ij))

theorem prodCover_ι (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))
    (hcov : ⨆ ij : 𝔄.ι × 𝔅.ι, 𝔄.U ij.1 ⊓ 𝔅.U ij.2 = ⊤) : (𝔄.prodCover 𝔅 haff hcov).ι = (𝔄.ι ×ₗ 𝔅.ι) := rfl

theorem prodCover_U (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))
    (hcov : ⨆ ij : 𝔄.ι × 𝔅.ι, 𝔄.U ij.1 ⊓ 𝔅.U ij.2 = ⊤) (ij : 𝔄.ι ×ₗ 𝔅.ι) :
    (𝔄.prodCover 𝔅 haff hcov).U ij = 𝔄.U (ofLex ij).1 ⊓ 𝔅.U (ofLex ij).2 := rfl

end Scheme.OrderedOpenFamily

namespace Scheme.OrderedAffineCover

def toOpenFamily {Z : Scheme.{u}} (K : Z.OrderedAffineCover) : Z.OrderedOpenFamily where
  ι := K.ι
  U := K.U

theorem toOpenFamily_ι {Z : Scheme.{u}} (K : Z.OrderedAffineCover) : K.toOpenFamily.ι = K.ι := rfl
theorem toOpenFamily_U {Z : Scheme.{u}} (K : Z.OrderedAffineCover) (i : K.ι) : K.toOpenFamily.U i = K.U i := rfl

def imageFamily {W Z : Scheme.{u}} (K : W.OrderedAffineCover) (f : W ⟶ Z) [IsOpenImmersion f] :
    Z.OrderedOpenFamily where
  ι := K.ι
  U i := f ''ᵁ K.U i

theorem imageFamily_ι {W Z : Scheme.{u}} (K : W.OrderedAffineCover) (f : W ⟶ Z) [IsOpenImmersion f] :
    (K.imageFamily f).ι = K.ι := rfl
theorem imageFamily_U {W Z : Scheme.{u}} (K : W.OrderedAffineCover) (f : W ⟶ Z) [IsOpenImmersion f] (i : K.ι) :
    (K.imageFamily f).U i = f ''ᵁ K.U i := rfl

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {π : Z ⟶ Spec (.of R)} (F : OModulePresheaf π)
variable (𝔄 𝔅 : Z.OrderedOpenFamily)

namespace BiCech

theorem inter_inf_le_left {p q : ℕ} (s : 𝔄.Idx (p + 1)) (t : 𝔅.Idx q) (j : Fin (p + 2)) :
    𝔄.inter s ⊓ 𝔅.inter t ≤ 𝔄.inter (𝔄.face s j) ⊓ 𝔅.inter t :=
  inf_le_inf_right _ (𝔄.inter_le_inter_face s j)

theorem inter_inf_le_right {p q : ℕ} (s : 𝔄.Idx p) (t : 𝔅.Idx (q + 1)) (j : Fin (q + 2)) :
    𝔄.inter s ⊓ 𝔅.inter t ≤ 𝔄.inter s ⊓ 𝔅.inter (𝔅.face t j) :=
  inf_le_inf_left _ (𝔅.inter_le_inter_face t j)

abbrev C (p q : ℕ) : Type u := ∀ st : 𝔄.Idx p × 𝔅.Idx q, F.obj (𝔄.inter st.1 ⊓ 𝔅.inter st.2)

def dH (p q : ℕ) : C F 𝔄 𝔅 p q →ₗ[R] C F 𝔄 𝔅 (p + 1) q :=
  LinearMap.pi fun st => ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((F.res (inter_inf_le_left 𝔄 𝔅 st.1 st.2 j)).comp (LinearMap.proj (𝔄.face st.1 j, st.2)))

def dV (p q : ℕ) : C F 𝔄 𝔅 p q →ₗ[R] C F 𝔄 𝔅 p (q + 1) :=
  LinearMap.pi fun st => ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((F.res (inter_inf_le_right 𝔄 𝔅 st.1 st.2 j)).comp (LinearMap.proj (st.1, 𝔅.face st.2 j)))

theorem dH_apply (p q : ℕ) (c : C F 𝔄 𝔅 p q) (st : 𝔄.Idx (p + 1) × 𝔅.Idx q) :
    dH F 𝔄 𝔅 p q c st = ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      F.res (inter_inf_le_left 𝔄 𝔅 st.1 st.2 j) (c (𝔄.face st.1 j, st.2)) := by
  simp only [dH, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

theorem dV_apply (p q : ℕ) (c : C F 𝔄 𝔅 p q) (st : 𝔄.Idx p × 𝔅.Idx (q + 1)) :
    dV F 𝔄 𝔅 p q c st = ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      F.res (inter_inf_le_right 𝔄 𝔅 st.1 st.2 j) (c (st.1, 𝔅.face st.2 j)) := by
  simp only [dV, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

theorem succAbove_comp_succAbove {n : ℕ} {i j : Fin (n + 2)} (H : i ≤ j) :
    Fin.succAbove j.succ ∘ Fin.succAbove i = Fin.succAbove i.castSucc ∘ Fin.succAbove j := by
  ext k
  simp only [Function.comp_apply, Fin.succAbove]
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩; rcases k with ⟨k, hk⟩
  simp only [Fin.le_def] at H
  simp only [Fin.lt_def, Fin.castSucc_mk, Fin.succ_mk, Fin.val_castSucc]
  split_ifs <;> simp_all only [Fin.val_succ, Fin.val_castSucc] <;> omega

theorem res_left_eq {p q : ℕ} {s s' : 𝔄.Idx p} (heq : s = s') (t : 𝔅.Idx q) (f : C F 𝔄 𝔅 p q)
    {O : Z.Opens} (h : O ≤ 𝔄.inter s ⊓ 𝔅.inter t) (h' : O ≤ 𝔄.inter s' ⊓ 𝔅.inter t) :
    F.res h (f (s, t)) = F.res h' (f (s', t)) := by
  subst heq; rfl

theorem res_right_eq {p q : ℕ} (s : 𝔄.Idx p) {t t' : 𝔅.Idx q} (heq : t = t') (f : C F 𝔄 𝔅 p q)
    {O : Z.Opens} (h : O ≤ 𝔄.inter s ⊓ 𝔅.inter t) (h' : O ≤ 𝔄.inter s ⊓ 𝔅.inter t') :
    F.res h (f (s, t)) = F.res h' (f (s, t')) := by
  subst heq; rfl

theorem dH_sq (p q : ℕ) : dH F 𝔄 𝔅 (p + 1) q ∘ₗ dH F 𝔄 𝔅 p q = 0 := by
  refine LinearMap.ext fun f => funext fun st => ?_
  obtain ⟨s, t⟩ := st
  rw [LinearMap.comp_apply, dH_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [dH_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul, ← pow_add]
  have hres : ∀ (a : Fin (p + 3)) (b : Fin (p + 2)),
      F.res (inter_inf_le_left 𝔄 𝔅 s t a)
          (F.res (inter_inf_le_left 𝔄 𝔅 (𝔄.face s a) t b) (f (𝔄.face (𝔄.face s a) b, t)))
        = F.res ((inter_inf_le_left 𝔄 𝔅 s t a).trans (inter_inf_le_left 𝔄 𝔅 (𝔄.face s a) t b))
            (f (𝔄.face (𝔄.face s a) b, t)) :=
    fun a b => (congrFun (congrArg DFunLike.coe (F.res_comp _ _)) _).symm
  simp only [hres]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  set S : Finset (Fin (p + 3) × Fin (p + 2)) := {ab | (ab.1 : ℕ) ≤ (ab.2 : ℕ)}
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
    set a' : Fin (p + 2) := Fin.castLT a (Nat.lt_of_le_of_lt hba b.isLt)
    have halt : a' ≤ b := Fin.le_def.mpr (by simpa [a'] using hba)
    have hacs : a'.castSucc = a := Fin.eq_of_val_eq (by simp [a'])
    have hface : 𝔄.face (𝔄.face s a) b = 𝔄.face (𝔄.face s b.succ) a' := by
      apply Subtype.ext
      change s.1 ∘ (Fin.succAbove a ∘ Fin.succAbove b) = s.1 ∘ (Fin.succAbove b.succ ∘ Fin.succAbove a')
      rw [← hacs, succAbove_comp_succAbove halt]
    have hsign : ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ)))
        = -((-1 : ℤ) ^ (((b.succ : Fin (p + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show ((b : ℕ) + 1 + (a : ℕ)) = ((a : ℕ) + (b : ℕ)) + 1 from by ring, pow_succ]; ring
    rw [hsign, neg_smul]
    refine congrArg Neg.neg (congrArg₂ (· • ·) (by congr 1) ?_)
    exact res_left_eq F 𝔄 𝔅 hface t f _ _

theorem dV_sq (p q : ℕ) : dV F 𝔄 𝔅 p (q + 1) ∘ₗ dV F 𝔄 𝔅 p q = 0 := by
  refine LinearMap.ext fun f => funext fun st => ?_
  obtain ⟨s, t⟩ := st
  rw [LinearMap.comp_apply, dV_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [dV_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul, ← pow_add]
  have hres : ∀ (a : Fin (q + 3)) (b : Fin (q + 2)),
      F.res (inter_inf_le_right 𝔄 𝔅 s t a)
          (F.res (inter_inf_le_right 𝔄 𝔅 s (𝔅.face t a) b) (f (s, 𝔅.face (𝔅.face t a) b)))
        = F.res ((inter_inf_le_right 𝔄 𝔅 s t a).trans (inter_inf_le_right 𝔄 𝔅 s (𝔅.face t a) b))
            (f (s, 𝔅.face (𝔅.face t a) b)) :=
    fun a b => (congrFun (congrArg DFunLike.coe (F.res_comp _ _)) _).symm
  simp only [hres]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  set S : Finset (Fin (q + 3) × Fin (q + 2)) := {ab | (ab.1 : ℕ) ≤ (ab.2 : ℕ)}
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
    set a' : Fin (q + 2) := Fin.castLT a (Nat.lt_of_le_of_lt hba b.isLt)
    have halt : a' ≤ b := Fin.le_def.mpr (by simpa [a'] using hba)
    have hacs : a'.castSucc = a := Fin.eq_of_val_eq (by simp [a'])
    have hface : 𝔅.face (𝔅.face t a) b = 𝔅.face (𝔅.face t b.succ) a' := by
      apply Subtype.ext
      change t.1 ∘ (Fin.succAbove a ∘ Fin.succAbove b) = t.1 ∘ (Fin.succAbove b.succ ∘ Fin.succAbove a')
      rw [← hacs, succAbove_comp_succAbove halt]
    have hsign : ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ)))
        = -((-1 : ℤ) ^ (((b.succ : Fin (q + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show ((b : ℕ) + 1 + (a : ℕ)) = ((a : ℕ) + (b : ℕ)) + 1 from by ring, pow_succ]; ring
    rw [hsign, neg_smul]
    refine congrArg Neg.neg (congrArg₂ (· • ·) (by congr 1) ?_)
    exact res_right_eq F 𝔄 𝔅 s hface f _ _

theorem dHV_comm (p q : ℕ) :
    dV F 𝔄 𝔅 (p + 1) q ∘ₗ dH F 𝔄 𝔅 p q = dH F 𝔄 𝔅 p (q + 1) ∘ₗ dV F 𝔄 𝔅 p q := by
  refine LinearMap.ext fun f => funext fun st => ?_
  obtain ⟨s, t⟩ := st
  simp only [LinearMap.comp_apply, dH_apply, dV_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul,
    OModulePresheaf.res_res]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

end BiCech

@[reducible] def biCech : DoubleComplex.Bounded R where
  C := BiCech.C F 𝔄 𝔅
  dH := BiCech.dH F 𝔄 𝔅
  dV := BiCech.dV F 𝔄 𝔅
  dH_sq := BiCech.dH_sq F 𝔄 𝔅
  dV_sq := BiCech.dV_sq F 𝔄 𝔅
  dHV_comm := BiCech.dHV_comm F 𝔄 𝔅
  N := max (Fintype.card 𝔄.ι) (Fintype.card 𝔅.ι)
  hBound p q h := by
    rcases h with h | h
    · haveI := 𝔄.isEmpty_idx_of_card_le ((le_max_left _ _).trans h)
      infer_instance
    · haveI := 𝔅.isEmpty_idx_of_card_le ((le_max_right _ _).trans h)
      infer_instance

theorem biCech_C (p q : ℕ) : (F.biCech 𝔄 𝔅).C p q = BiCech.C F 𝔄 𝔅 p q := rfl
theorem biCech_N : (F.biCech 𝔄 𝔅).N = max (Fintype.card 𝔄.ι) (Fintype.card 𝔅.ι) := rfl
theorem biCech_dH (p q : ℕ) : (F.biCech 𝔄 𝔅).dH p q = BiCech.dH F 𝔄 𝔅 p q := rfl
theorem biCech_dV (p q : ℕ) : (F.biCech 𝔄 𝔅).dV p q = BiCech.dV F 𝔄 𝔅 p q := rfl

end OModulePresheaf

end AlgebraicGeometry

end


