-- Prove2me | Definitions.Def_AlgebraicGeometry_IterCech
-- name    : AlgebraicGeometry_IterCech
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/62437e24-c221-5f56-af5e-9470a18c36cd
-- title:
--   Iterated Čech double complex for three ordered open families
-- statement:
--   Fix a commutative ring $R$, a scheme $Z$ with a morphism $\pi\colon Z\to\operatorname{Spec} R$, an `OModulePresheaf` $F$ over $\pi$ (a family of $R$-modules $F(U)$ indexed by the opens of $Z$, each a module over $\Gamma(Z,U)$ compatibly, with $R$-linear restriction maps satisfying the reflexivity and transitivity identities), and three finite ordered families $\mathfrak A,\mathfrak B,\mathfrak C$ of opens of $Z$ (`Scheme.OrderedOpenFamily`: a finite linearly ordered index set and an assignment of opens). First, `Scheme.OrderedOpenFamily.restr` forms $\mathfrak B\cap W=(B_j\cap W)_j$ for an open $W$, together with the comparisons $\bigcap_t(B\cap W)\le(\bigcap_t B)\cap W$, its converse, and monotonicity in $W$. On these, `IterCech.resC` and `IterCech.resTot` are the restriction maps $\mathrm{Tot}^m\check C(F;\mathfrak A,\mathfrak B\cap W')\to\mathrm{Tot}^m\check C(F;\mathfrak A,\mathfrak B\cap W)$ for $W\le W'$, shown to be functorial in $W$ and to commute with the bi-Čech differentials and with the total differential [`DoubleComplex.dTot`](../def/AlgebraicGeometry_DoubleComplex.html#L55).
--
--   The main object is `IterCech.C F 𝔄 𝔅 ℭ r m` $= \prod_{k_0<\cdots<k_r}\mathrm{Tot}^m\check C(F;\mathfrak A,\mathfrak B\cap C_K)$, i.e. $\prod_K\prod_{p+q=m}\prod_{s,t}F(A_s\cap(B_t\cap C_K))$, with `dH` the alternating sum over the faces of $K$ of the restriction maps `resTot`, and `dV` the total differential of the bi-Čech double complex on each factor. The identities `dH_sq`, `dV_sq` and `dHV_comm` (the face-comparison of `dH_sq` resting on the commutation of `Fin.succAbove` maps) assemble this into `OModulePresheaf.iterCech F 𝔄 𝔅 ℭ : DoubleComplex.Bounded R`, whose bound field $N$ is $\#\mathfrak A.\iota+\#\mathfrak B.\iota+\#\mathfrak C.\iota$, the vanishing beyond it coming from emptiness of the index sets of strictly increasing chains. Two augmentations are provided: `resTot₀`, `augTot` send $\mathrm{Tot}^m\check C(F;\mathfrak A,\mathfrak B)$ into the $r=0$ column by restriction to each $C_k$, commuting with the vertical differentials and annihilated by `dH`; and, for an ordered affine cover $\mathfrak C'$, `augCech` sends the Čech cochains $\prod_K F(C_K)$ into the $m=0$ row by restriction to each $A_s\cap(B_t\cap C_K)$, intertwining the Čech differential `F.d` with `dH`.
--
--   **Relation to Mathlib.** Mathlib's Čech machinery is simplicial and sheaf-theoretic; the ordered-chain Čech and bi-Čech complexes of `OModulePresheaf`, and the bounded double complexes of [`DoubleComplex.Bounded`](../def/AlgebraicGeometry_DoubleComplex.html#L11) used here, are the project's own constructions.
--
--   **Where it is used.** The iterated complex is the Cartan–Leray device for comparing the bi-Čech complex of two ordered families with the Čech complex of a third (for instance a product cover), which underlies the cohomological finiteness and base-change statements about coherent modules on schemes needed downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_IterCech.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

namespace Scheme.OrderedOpenFamily

variable {Z : Scheme.{u}} (𝔅 : Z.OrderedOpenFamily)

def restr (W : Z.Opens) : Z.OrderedOpenFamily where
  ι := 𝔅.ι
  U j := 𝔅.U j ⊓ W

theorem restr_ι (W : Z.Opens) : (𝔅.restr W).ι = 𝔅.ι := rfl
theorem restr_U (W : Z.Opens) (j : 𝔅.ι) : (𝔅.restr W).U j = 𝔅.U j ⊓ W := rfl

theorem restr_inter_mono {W W' : Z.Opens} (h : W ≤ W') {q : ℕ} (t : 𝔅.Idx q) :
    (𝔅.restr W).inter (show (𝔅.restr W).Idx q from t) ≤ (𝔅.restr W').inter (show (𝔅.restr W').Idx q from t) :=
  le_iInf fun j => (iInf_le _ j).trans (inf_le_inf_left _ h)

theorem restr_inter_le (W : Z.Opens) {q : ℕ} (t : 𝔅.Idx q) :
    (𝔅.restr W).inter (show (𝔅.restr W).Idx q from t) ≤ 𝔅.inter t ⊓ W :=
  le_inf (le_iInf fun j => (iInf_le _ j).trans inf_le_left) ((iInf_le _ 0).trans inf_le_right)

theorem le_restr_inter (W : Z.Opens) {q : ℕ} (t : 𝔅.Idx q) :
    𝔅.inter t ⊓ W ≤ (𝔅.restr W).inter (show (𝔅.restr W).Idx q from t) :=
  le_iInf fun j => inf_le_inf_right _ (iInf_le _ j)

end Scheme.OrderedOpenFamily

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {π : Z ⟶ Spec (.of R)} (F : OModulePresheaf π)
variable (𝔄 𝔅 ℭ : Z.OrderedOpenFamily)

namespace IterCech

def resC {W W' : Z.Opens} (h : W ≤ W') (p q : ℕ) :
    BiCech.C F 𝔄 (𝔅.restr W') p q →ₗ[R] BiCech.C F 𝔄 (𝔅.restr W) p q :=
  LinearMap.pi fun st => (F.res (inf_le_inf_left _ (𝔅.restr_inter_mono h st.2))).comp (LinearMap.proj st)

theorem resC_apply {W W' : Z.Opens} (h : W ≤ W') (p q : ℕ) (c : BiCech.C F 𝔄 (𝔅.restr W') p q)
    (st : 𝔄.Idx p × (𝔅.restr W).Idx q) :
    resC F 𝔄 𝔅 h p q c st = F.res (inf_le_inf_left _ (𝔅.restr_inter_mono h st.2)) (c st) := rfl

theorem resC_comp_dH {W W' : Z.Opens} (h : W ≤ W') (p q : ℕ) :
    resC F 𝔄 𝔅 h (p + 1) q ∘ₗ BiCech.dH F 𝔄 (𝔅.restr W') p q
      = BiCech.dH F 𝔄 (𝔅.restr W) p q ∘ₗ resC F 𝔄 𝔅 h p q := by
  refine LinearMap.ext fun c => funext fun st => ?_
  simp only [LinearMap.comp_apply, resC_apply, BiCech.dH_apply, map_sum, map_zsmul, OModulePresheaf.res_res]
  rfl

theorem resC_comp_dV {W W' : Z.Opens} (h : W ≤ W') (p q : ℕ) :
    resC F 𝔄 𝔅 h p (q + 1) ∘ₗ BiCech.dV F 𝔄 (𝔅.restr W') p q
      = BiCech.dV F 𝔄 (𝔅.restr W) p q ∘ₗ resC F 𝔄 𝔅 h p q := by
  refine LinearMap.ext fun c => funext fun st => ?_
  simp only [LinearMap.comp_apply, resC_apply, BiCech.dV_apply, map_sum, map_zsmul, OModulePresheaf.res_res]
  rfl

def resTot {W W' : Z.Opens} (h : W ≤ W') (m : ℕ) :
    DoubleComplex.Tot (F.biCech 𝔄 (𝔅.restr W')) m →ₗ[R] DoubleComplex.Tot (F.biCech 𝔄 (𝔅.restr W)) m :=
  LinearMap.pi fun pq => (resC F 𝔄 𝔅 h pq.1.1 pq.1.2).comp (LinearMap.proj pq)

theorem resTot_apply {W W' : Z.Opens} (h : W ≤ W') (m : ℕ)
    (c : DoubleComplex.Tot (F.biCech 𝔄 (𝔅.restr W')) m) (pq : DoubleComplex.Diag m)
    (st : 𝔄.Idx pq.1.1 × (𝔅.restr W).Idx pq.1.2) :
    resTot F 𝔄 𝔅 h m c pq st = F.res (inf_le_inf_left _ (𝔅.restr_inter_mono h st.2)) (c pq st) := rfl

theorem resTot_refl (W : Z.Opens) (m : ℕ) : resTot F 𝔄 𝔅 (le_refl W) m = LinearMap.id := by
  refine LinearMap.ext fun c => funext fun pq => funext fun st => ?_
  rw [resTot_apply]; exact F.res_refl_apply _ _

theorem resTot_comp {W W' W'' : Z.Opens} (h : W ≤ W') (h' : W' ≤ W'') (m : ℕ) :
    resTot F 𝔄 𝔅 h m ∘ₗ resTot F 𝔄 𝔅 h' m = resTot F 𝔄 𝔅 (h.trans h') m := by
  refine LinearMap.ext fun c => funext fun pq => funext fun st => ?_
  show F.res _ (F.res _ (c pq st)) = F.res _ (c pq st)
  rw [F.res_res]

theorem resTot_comp_dTot {W W' : Z.Opens} (h : W ≤ W') (m : ℕ) :
    resTot F 𝔄 𝔅 h (m + 1) ∘ₗ DoubleComplex.dTot (F.biCech 𝔄 (𝔅.restr W')) m
      = DoubleComplex.dTot (F.biCech 𝔄 (𝔅.restr W)) m ∘ₗ resTot F 𝔄 𝔅 h m := by
  refine LinearMap.ext fun c => funext fun pq => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rcases p with _ | p' <;> rcases q with _ | q'
  · exfalso; simp only at hpq; omega
  · show resC F 𝔄 𝔅 h _ _ (DoubleComplex.dTot _ m c ⟨(0, q' + 1), hpq⟩) = _
    rw [DoubleComplex.dTot_apply_zero_succ, DoubleComplex.dTot_apply_zero_succ, biCech_dV, biCech_dV,
      ← LinearMap.comp_apply, resC_comp_dV]
    rfl
  · show resC F 𝔄 𝔅 h _ _ (DoubleComplex.dTot _ m c ⟨(p' + 1, 0), hpq⟩) = _
    rw [DoubleComplex.dTot_apply_succ_zero, DoubleComplex.dTot_apply_succ_zero, biCech_dH, biCech_dH,
      ← LinearMap.comp_apply, resC_comp_dH]
    rfl
  · show resC F 𝔄 𝔅 h _ _ (DoubleComplex.dTot _ m c ⟨(p' + 1, q' + 1), hpq⟩) = _
    rw [DoubleComplex.dTot_apply_succ_succ, DoubleComplex.dTot_apply_succ_succ, biCech_dH, biCech_dH,
      biCech_dV, biCech_dV, map_add, map_zsmul, ← LinearMap.comp_apply, resC_comp_dH, ← LinearMap.comp_apply,
      resC_comp_dV]
    rfl

abbrev C (r m : ℕ) : Type u := ∀ K : ℭ.Idx r, DoubleComplex.Tot (F.biCech 𝔄 (𝔅.restr (ℭ.inter K))) m

def dH (r m : ℕ) : C F 𝔄 𝔅 ℭ r m →ₗ[R] C F 𝔄 𝔅 ℭ (r + 1) m :=
  LinearMap.pi fun K => ∑ j : Fin (r + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((resTot F 𝔄 𝔅 (ℭ.inter_le_inter_face K j) m).comp (LinearMap.proj (ℭ.face K j)))

def dV (r m : ℕ) : C F 𝔄 𝔅 ℭ r m →ₗ[R] C F 𝔄 𝔅 ℭ r (m + 1) :=
  LinearMap.pi fun K => (DoubleComplex.dTot (F.biCech 𝔄 (𝔅.restr (ℭ.inter K))) m).comp (LinearMap.proj K)

theorem dH_apply (r m : ℕ) (c : C F 𝔄 𝔅 ℭ r m) (K : ℭ.Idx (r + 1)) :
    dH F 𝔄 𝔅 ℭ r m c K = ∑ j : Fin (r + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      resTot F 𝔄 𝔅 (ℭ.inter_le_inter_face K j) m (c (ℭ.face K j)) := by
  simp only [dH, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

theorem dV_apply (r m : ℕ) (c : C F 𝔄 𝔅 ℭ r m) (K : ℭ.Idx r) :
    dV F 𝔄 𝔅 ℭ r m c K = DoubleComplex.dTot (F.biCech 𝔄 (𝔅.restr (ℭ.inter K))) m (c K) := rfl

theorem succAbove_comp_succAbove' {n : ℕ} {i j : Fin (n + 2)} (H : i ≤ j) :
    Fin.succAbove j.succ ∘ Fin.succAbove i = Fin.succAbove i.castSucc ∘ Fin.succAbove j :=
  BiCech.succAbove_comp_succAbove H

theorem resTot_at_eq {r m : ℕ} {K K' : ℭ.Idx r} (heq : K = K') (c : C F 𝔄 𝔅 ℭ r m) {W : Z.Opens}
    (h : W ≤ ℭ.inter K) (h' : W ≤ ℭ.inter K') :
    resTot F 𝔄 𝔅 h m (c K) = resTot F 𝔄 𝔅 h' m (c K') := by
  subst heq; rfl

theorem dH_sq (r m : ℕ) : dH F 𝔄 𝔅 ℭ (r + 1) m ∘ₗ dH F 𝔄 𝔅 ℭ r m = 0 := by
  refine LinearMap.ext fun f => funext fun K => ?_
  rw [LinearMap.comp_apply, dH_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [dH_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul, ← pow_add]
  have hres : ∀ (a : Fin (r + 3)) (b : Fin (r + 2)),
      resTot F 𝔄 𝔅 (ℭ.inter_le_inter_face K a) m
          (resTot F 𝔄 𝔅 (ℭ.inter_le_inter_face (ℭ.face K a) b) m (f (ℭ.face (ℭ.face K a) b)))
        = resTot F 𝔄 𝔅 ((ℭ.inter_le_inter_face K a).trans (ℭ.inter_le_inter_face (ℭ.face K a) b)) m
            (f (ℭ.face (ℭ.face K a) b)) :=
    fun a b => (congrFun (congrArg DFunLike.coe (resTot_comp F 𝔄 𝔅 (ℭ.inter_le_inter_face K a)
      (ℭ.inter_le_inter_face (ℭ.face K a) b) m)) _)
  simp only [hres]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  set S : Finset (Fin (r + 3) × Fin (r + 2)) := {ab | (ab.1 : ℕ) ≤ (ab.2 : ℕ)}
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
    set a' : Fin (r + 2) := Fin.castLT a (Nat.lt_of_le_of_lt hba b.isLt)
    have halt : a' ≤ b := Fin.le_def.mpr (by simpa [a'] using hba)
    have hacs : a'.castSucc = a := Fin.eq_of_val_eq (by simp [a'])
    have hface : ℭ.face (ℭ.face K a) b = ℭ.face (ℭ.face K b.succ) a' := by
      apply Subtype.ext
      change K.1 ∘ (Fin.succAbove a ∘ Fin.succAbove b) = K.1 ∘ (Fin.succAbove b.succ ∘ Fin.succAbove a')
      rw [← hacs, succAbove_comp_succAbove' halt]
    have hsign : ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ)))
        = -((-1 : ℤ) ^ (((b.succ : Fin (r + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show ((b : ℕ) + 1 + (a : ℕ)) = ((a : ℕ) + (b : ℕ)) + 1 from by ring, pow_succ]; ring
    rw [hsign, neg_smul]
    refine congrArg Neg.neg (congrArg₂ (· • ·) (by congr 1) ?_)
    exact resTot_at_eq F 𝔄 𝔅 ℭ hface f _ _

theorem dV_sq (r m : ℕ) : dV F 𝔄 𝔅 ℭ r (m + 1) ∘ₗ dV F 𝔄 𝔅 ℭ r m = 0 := by
  refine LinearMap.ext fun c => funext fun K => ?_
  show DoubleComplex.dTot _ (m + 1) (DoubleComplex.dTot _ m (c K)) = 0
  rw [← LinearMap.comp_apply, DoubleComplex.dTot_comp_dTot]; rfl

theorem dHV_comm (r m : ℕ) :
    dV F 𝔄 𝔅 ℭ (r + 1) m ∘ₗ dH F 𝔄 𝔅 ℭ r m = dH F 𝔄 𝔅 ℭ r (m + 1) ∘ₗ dV F 𝔄 𝔅 ℭ r m := by
  refine LinearMap.ext fun c => funext fun K => ?_
  show DoubleComplex.dTot _ m (dH F 𝔄 𝔅 ℭ r m c K) = dH F 𝔄 𝔅 ℭ r (m + 1) (dV F 𝔄 𝔅 ℭ r m c) K
  rw [dH_apply, dH_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, dV_apply, ← LinearMap.comp_apply, ← resTot_comp_dTot]
  rfl

def resC₀ (W : Z.Opens) (p q : ℕ) : BiCech.C F 𝔄 𝔅 p q →ₗ[R] BiCech.C F 𝔄 (𝔅.restr W) p q where
  toFun c := fun st => F.res (inf_le_inf_left _ (le_trans (𝔅.restr_inter_le W st.2) inf_le_left))
    (c st)
  map_add' c c' := funext fun _ => map_add (F.res _) (c _) (c' _)
  map_smul' a c := funext fun _ => LinearMap.map_smul (F.res _) a (c _)

theorem resC₀_apply (W : Z.Opens) (p q : ℕ) (c : BiCech.C F 𝔄 𝔅 p q) (st : 𝔄.Idx p × (𝔅.restr W).Idx q) :
    resC₀ F 𝔄 𝔅 W p q c st = F.res (inf_le_inf_left _ (le_trans (𝔅.restr_inter_le W st.2) inf_le_left))
      (c st) := rfl

theorem resC₀_comp_dH (W : Z.Opens) (p q : ℕ) :
    resC₀ F 𝔄 𝔅 W (p + 1) q ∘ₗ BiCech.dH F 𝔄 𝔅 p q = BiCech.dH F 𝔄 (𝔅.restr W) p q ∘ₗ resC₀ F 𝔄 𝔅 W p q := by
  refine LinearMap.ext fun c => funext fun st => ?_
  simp only [LinearMap.comp_apply, resC₀_apply, BiCech.dH_apply, map_sum, map_zsmul, OModulePresheaf.res_res]
  rfl

theorem resC₀_comp_dV (W : Z.Opens) (p q : ℕ) :
    resC₀ F 𝔄 𝔅 W p (q + 1) ∘ₗ BiCech.dV F 𝔄 𝔅 p q = BiCech.dV F 𝔄 (𝔅.restr W) p q ∘ₗ resC₀ F 𝔄 𝔅 W p q := by
  refine LinearMap.ext fun c => funext fun st => ?_
  simp only [LinearMap.comp_apply, resC₀_apply, BiCech.dV_apply, map_sum, map_zsmul, OModulePresheaf.res_res]
  rfl

def resTot₀ (W : Z.Opens) (m : ℕ) :
    DoubleComplex.Tot (F.biCech 𝔄 𝔅) m →ₗ[R] DoubleComplex.Tot (F.biCech 𝔄 (𝔅.restr W)) m :=
  LinearMap.pi fun pq => (resC₀ F 𝔄 𝔅 W pq.1.1 pq.1.2).comp (LinearMap.proj pq)

theorem resTot₀_apply (W : Z.Opens) (m : ℕ) (c : DoubleComplex.Tot (F.biCech 𝔄 𝔅) m)
    (pq : DoubleComplex.Diag m) (st : 𝔄.Idx pq.1.1 × (𝔅.restr W).Idx pq.1.2) :
    resTot₀ F 𝔄 𝔅 W m c pq st = F.res (inf_le_inf_left _ (le_trans (𝔅.restr_inter_le W st.2) inf_le_left))
      (c pq st) := rfl

theorem resTot₀_comp_dTot (W : Z.Opens) (m : ℕ) :
    resTot₀ F 𝔄 𝔅 W (m + 1) ∘ₗ DoubleComplex.dTot (F.biCech 𝔄 𝔅) m
      = DoubleComplex.dTot (F.biCech 𝔄 (𝔅.restr W)) m ∘ₗ resTot₀ F 𝔄 𝔅 W m := by
  refine LinearMap.ext fun c => funext fun pq => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rcases p with _ | p' <;> rcases q with _ | q'
  · exfalso; simp only at hpq; omega
  · show resC₀ F 𝔄 𝔅 W _ _ (DoubleComplex.dTot _ m c ⟨(0, q' + 1), hpq⟩) = _
    rw [DoubleComplex.dTot_apply_zero_succ, DoubleComplex.dTot_apply_zero_succ, biCech_dV, biCech_dV,
      ← LinearMap.comp_apply, resC₀_comp_dV]
    rfl
  · show resC₀ F 𝔄 𝔅 W _ _ (DoubleComplex.dTot _ m c ⟨(p' + 1, 0), hpq⟩) = _
    rw [DoubleComplex.dTot_apply_succ_zero, DoubleComplex.dTot_apply_succ_zero, biCech_dH, biCech_dH,
      ← LinearMap.comp_apply, resC₀_comp_dH]
    rfl
  · show resC₀ F 𝔄 𝔅 W _ _ (DoubleComplex.dTot _ m c ⟨(p' + 1, q' + 1), hpq⟩) = _
    rw [DoubleComplex.dTot_apply_succ_succ, DoubleComplex.dTot_apply_succ_succ, biCech_dH, biCech_dH,
      biCech_dV, biCech_dV, map_add, map_zsmul, ← LinearMap.comp_apply, resC₀_comp_dH, ← LinearMap.comp_apply,
      resC₀_comp_dV]
    rfl

theorem resTot_comp_resTot₀ {W W' : Z.Opens} (h : W ≤ W') (m : ℕ) :
    resTot F 𝔄 𝔅 h m ∘ₗ resTot₀ F 𝔄 𝔅 W' m = resTot₀ F 𝔄 𝔅 W m := by
  refine LinearMap.ext fun c => funext fun pq => funext fun st => ?_
  show F.res _ (F.res _ (c pq _)) = F.res _ (c pq _)
  rw [F.res_res]

def augTot (m : ℕ) : DoubleComplex.Tot (F.biCech 𝔄 𝔅) m →ₗ[R] C F 𝔄 𝔅 ℭ 0 m :=
  LinearMap.pi fun K => resTot₀ F 𝔄 𝔅 (ℭ.inter K) m

theorem augTot_apply (m : ℕ) (c : DoubleComplex.Tot (F.biCech 𝔄 𝔅) m) (K : ℭ.Idx 0) :
    augTot F 𝔄 𝔅 ℭ m c K = resTot₀ F 𝔄 𝔅 (ℭ.inter K) m c := rfl

theorem dV_comp_augTot (m : ℕ) :
    dV F 𝔄 𝔅 ℭ 0 m ∘ₗ augTot F 𝔄 𝔅 ℭ m = augTot F 𝔄 𝔅 ℭ (m + 1) ∘ₗ DoubleComplex.dTot (F.biCech 𝔄 𝔅) m := by
  refine LinearMap.ext fun c => funext fun K => ?_
  show DoubleComplex.dTot _ m (resTot₀ F 𝔄 𝔅 (ℭ.inter K) m c) = resTot₀ F 𝔄 𝔅 (ℭ.inter K) (m + 1) _
  rw [← LinearMap.comp_apply, ← resTot₀_comp_dTot]; rfl

theorem dH_comp_augTot (m : ℕ) : dH F 𝔄 𝔅 ℭ 0 m ∘ₗ augTot F 𝔄 𝔅 ℭ m = 0 := by
  refine LinearMap.ext fun c => funext fun K => ?_
  rw [LinearMap.comp_apply, dH_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [augTot_apply]
  have : ∀ j : Fin 2, resTot F 𝔄 𝔅 (ℭ.inter_le_inter_face K j) m (resTot₀ F 𝔄 𝔅 (ℭ.inter (ℭ.face K j)) m c)
      = resTot₀ F 𝔄 𝔅 (ℭ.inter K) m c :=
    fun j => congrFun (congrArg DFunLike.coe (resTot_comp_resTot₀ F 𝔄 𝔅 (ℭ.inter_le_inter_face K j) m)) c
  simp only [this]
  show (∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • resTot₀ F 𝔄 𝔅 (ℭ.inter K) m c) = 0
  simp [Fin.sum_univ_two]

def augCech (ℭ' : Z.OrderedAffineCover) (r : ℕ) : F.cochain ℭ' r →ₗ[R] C F 𝔄 𝔅 ℭ'.toOpenFamily r 0 where
  toFun x := fun K _ st =>
    F.res (show 𝔄.inter st.1 ⊓ (𝔅.restr (ℭ'.toOpenFamily.inter K)).inter st.2 ≤ ℭ'.inter K from
        le_trans inf_le_right (le_trans (𝔅.restr_inter_le _ st.2) inf_le_right))
      (x K)
  map_add' x x' := funext fun K => funext fun _ => funext fun _ => map_add (F.res _) (x K) (x' K)
  map_smul' a x := funext fun K => funext fun _ => funext fun _ => LinearMap.map_smul (F.res _) a (x K)

theorem augCech_apply (ℭ' : Z.OrderedAffineCover) (r : ℕ) (x : F.cochain ℭ' r) (K : ℭ'.toOpenFamily.Idx r)
    (pq : DoubleComplex.Diag 0) (st : 𝔄.Idx pq.1.1 × (𝔅.restr (ℭ'.toOpenFamily.inter K)).Idx pq.1.2) :
    augCech F 𝔄 𝔅 ℭ' r x K pq st
      = F.res (show 𝔄.inter st.1 ⊓ (𝔅.restr (ℭ'.toOpenFamily.inter K)).inter st.2 ≤ ℭ'.inter K from
          le_trans inf_le_right (le_trans (𝔅.restr_inter_le _ st.2) inf_le_right)) (x K) := rfl

theorem dH_comp_augCech (ℭ' : Z.OrderedAffineCover) (r : ℕ) :
    dH F 𝔄 𝔅 ℭ'.toOpenFamily r 0 ∘ₗ augCech F 𝔄 𝔅 ℭ' r = augCech F 𝔄 𝔅 ℭ' (r + 1) ∘ₗ F.d ℭ' r := by
  refine LinearMap.ext fun x => funext fun K => funext fun pq => funext fun st => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, dH_apply, augCech_apply]
  show (∑ j : Fin (r + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      resTot F 𝔄 𝔅 (ℭ'.toOpenFamily.inter_le_inter_face K j) 0 (augCech F 𝔄 𝔅 ℭ' r x _)) pq st = _
  rw [OModulePresheaf.d_apply, map_sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, resTot_apply, augCech_apply, map_zsmul, OModulePresheaf.res_res,
    OModulePresheaf.res_res]
  rfl

end IterCech

@[reducible] def iterCech : DoubleComplex.Bounded R where
  C := IterCech.C F 𝔄 𝔅 ℭ
  dH := IterCech.dH F 𝔄 𝔅 ℭ
  dV := IterCech.dV F 𝔄 𝔅 ℭ
  dH_sq := IterCech.dH_sq F 𝔄 𝔅 ℭ
  dV_sq := IterCech.dV_sq F 𝔄 𝔅 ℭ
  dHV_comm := IterCech.dHV_comm F 𝔄 𝔅 ℭ
  N := Fintype.card 𝔄.ι + Fintype.card 𝔅.ι + Fintype.card ℭ.ι
  hBound r m h := by
    rcases h with h | h
    · haveI := ℭ.isEmpty_idx_of_card_le (show Fintype.card ℭ.ι ≤ r by omega)
      infer_instance
    · refine ⟨fun a b => funext fun K => funext fun pq => ?_⟩
      have : Subsingleton (BiCech.C F 𝔄 (𝔅.restr (ℭ.inter K)) pq.1.1 pq.1.2) := by
        rcases le_or_gt (Fintype.card 𝔄.ι) pq.1.1 with h1 | h1
        · haveI := 𝔄.isEmpty_idx_of_card_le h1; infer_instance
        · have h2 : Fintype.card 𝔅.ι ≤ pq.1.2 := by have := pq.2; omega
          haveI := (𝔅.restr (ℭ.inter K)).isEmpty_idx_of_card_le (p := pq.1.2) h2; infer_instance
      exact Subsingleton.elim _ _

theorem iterCech_C (r m : ℕ) : (F.iterCech 𝔄 𝔅 ℭ).C r m = IterCech.C F 𝔄 𝔅 ℭ r m := rfl
theorem iterCech_dH (r m : ℕ) : (F.iterCech 𝔄 𝔅 ℭ).dH r m = IterCech.dH F 𝔄 𝔅 ℭ r m := rfl
theorem iterCech_dV (r m : ℕ) : (F.iterCech 𝔄 𝔅 ℭ).dV r m = IterCech.dV F 𝔄 𝔅 ℭ r m := rfl
theorem iterCech_N : (F.iterCech 𝔄 𝔅 ℭ).N = Fintype.card 𝔄.ι + Fintype.card 𝔅.ι + Fintype.card ℭ.ι := rfl

end OModulePresheaf

end AlgebraicGeometry

end


