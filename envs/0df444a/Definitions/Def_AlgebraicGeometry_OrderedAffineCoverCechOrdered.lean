-- Prove2me | Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
-- name    : AlgebraicGeometry_OrderedAffineCoverCechOrdered
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/7314eac5-e229-5792-9de8-1f612498a456
-- title:
--   Ordered Čech cochains for an ordered affine cover
-- statement:
--   Standing context: a scheme $V$ with an ordered affine cover $K$ (a finite linearly ordered index type $\iota$ together with affine opens $U_i$ whose supremum is $\top$), a morphism $\pi \colon V \to \operatorname{Spec} R$ over a commutative ring $R$, and a module presheaf $F$ on $\pi$, i.e. an assignment $U \mapsto F(U)$ of $R$-modules that are also $\Gamma(V,U)$-modules compatibly, with restriction maps $F(U') \to F(U)$ for $U \le U'$.
--
--   The index objects are the unrestricted tuples: `OIdx n` is all maps $t \colon \mathrm{Fin}(n+1) \to \iota$, with no monotonicity condition, and `ointer t` $= \bigcap_j U_{t_j}$. The face map `oface t j` is $t \circ \mathrm{succAbove}\,j$ (delete the $j$-th entry), and `ofrontFace`/`obackFace`, for $a+b=n$, are the initial segment $(t_0,\dots,t_a)$ and the terminal segment $(t_a,\dots,t_n)$; the accompanying lemmas record the evident inclusions of intersections, and that these formulas agree on the nose with the strictly increasing versions (`inter_eq_ointer`, `frontFace_val`, `backFace_val`). For injective $t$, `osort t` is the strictly increasing reordering $t \circ \mathrm{Tuple.sort}\,t$, with $\bigcap_j U_{t_j}$ equal to the intersection along the sorted tuple (both inequalities).
--
--   On cochains, `ocochain K n` $= \prod_{t : \mathrm{OIdx}\,n} F(\mathrm{ointer}\,t)$; `od` is the $R$-linear differential $(dc)(t) = \sum_{j}(-1)^j c(\mathrm{oface}\,t\,j)|_{\mathrm{ointer}\,t}$; `ocup` is the Alexander–Whitney product, pairing $\alpha$ in the cochains of the unit module presheaf `unit π` (sections of $\mathcal{O}_V$) with $\beta$ in those of $F$ by $\alpha(\mathrm{ofrontFace}\,t) \cdot \beta(\mathrm{obackFace}\,t)$, restricted to $\mathrm{ointer}\,t$. Two comparison maps with the increasing-chain complex are defined: `ores`, evaluation at increasing tuples, and `oext`, the alternating extension sending $z$ to $t \mapsto \mathrm{sign}(\mathrm{Tuple.sort}\,t)\, z(\mathrm{osort}\,t)|_{\mathrm{ointer}\,t}$ when $t$ is injective and to $0$ otherwise. Finally, for $h \colon X \to Y$ with ordered affine covers $\mathcal{W}$, $\mathcal{K}$ and an index map $\lambda$ satisfying $\mathcal{W}.U_w \le h^{-1}\mathcal{K}.U_{\lambda w}$, `ounitPullback` pulls back cochains of $\mathcal{O}_Y$ by $t \mapsto h^{\sharp}(c(\lambda \circ t))$ restricted along the inclusion $\mathcal{W}.\mathrm{ointer}\,t \le h^{-1}\mathcal{K}.\mathrm{ointer}(\lambda \circ t)$ supplied by `ointer_le_preimage_ointer_comp`; no sorting and no sign occur.
--
--   **Relation to Mathlib.** Mathlib has no Čech complex of this elementary shape for module presheaves on schemes; these ordered cochains, their differential, cup product and the comparison maps with the project's increasing-chain complex are the project's own.
--
--   **Where it is used.** These ordered cochains serve as an auxiliary complex for the project's Čech-theoretic treatment of module presheaves on schemes: the cup product and the functoriality in morphisms of schemes are easy to define on unrestricted tuples, and `ores`, `oext` transport them to the complex indexed by strictly increasing chains used for the finiteness and base-change results on coherent cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered.lean

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

abbrev OIdx (n : ℕ) : Type u := Fin (n + 1) → K.ι

def ointer {n : ℕ} (t : K.OIdx n) : V.Opens := ⨅ j, K.U (t j)

theorem inter_eq_ointer {n : ℕ} (s : K.Idx n) : K.inter s = K.ointer s.1 := rfl

theorem ointer_le {n : ℕ} (t : K.OIdx n) (j : Fin (n + 1)) : K.ointer t ≤ K.U (t j) := iInf_le _ j

def oface {n : ℕ} (t : K.OIdx (n + 1)) (j : Fin (n + 2)) : K.OIdx n := t ∘ Fin.succAbove j

theorem oface_apply {n : ℕ} (t : K.OIdx (n + 1)) (j : Fin (n + 2)) (k : Fin (n + 1)) :
    K.oface t j k = t (j.succAbove k) := rfl

theorem ointer_le_ointer_oface {n : ℕ} (t : K.OIdx (n + 1)) (j : Fin (n + 2)) :
    K.ointer t ≤ K.ointer (K.oface t j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

def ofrontFace (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) : K.OIdx a := fun j => t ⟨j.1, by omega⟩

def obackFace (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) : K.OIdx b := fun j => t ⟨a + j.1, by omega⟩

theorem ofrontFace_apply (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) (j : Fin (a + 1)) :
    K.ofrontFace a b n h t j = t ⟨j.1, by omega⟩ := rfl

theorem obackFace_apply (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) (j : Fin (b + 1)) :
    K.obackFace a b n h t j = t ⟨a + j.1, by omega⟩ := rfl

theorem frontFace_val (a b n : ℕ) (h : a + b = n) (s : K.Idx n) :
    (K.frontFace a b n h s).1 = K.ofrontFace a b n h s.1 := rfl

theorem backFace_val (a b n : ℕ) (h : a + b = n) (s : K.Idx n) :
    (K.backFace a b n h s).1 = K.obackFace a b n h s.1 := rfl

theorem ointer_le_ointer_ofrontFace (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) :
    K.ointer t ≤ K.ointer (K.ofrontFace a b n h t) :=
  le_iInf fun _ => iInf_le _ _

theorem ointer_le_ointer_obackFace (a b n : ℕ) (h : a + b = n) (t : K.OIdx n) :
    K.ointer t ≤ K.ointer (K.obackFace a b n h t) :=
  le_iInf fun _ => iInf_le _ _

def osort {n : ℕ} (t : K.OIdx n) (hinj : Function.Injective t) : K.Idx n :=
  ⟨t ∘ Tuple.sort t, (Tuple.monotone_sort t).strictMono_of_injective (hinj.comp (Tuple.sort t).injective)⟩

theorem osort_val {n : ℕ} (t : K.OIdx n) (hinj : Function.Injective t) :
    (K.osort t hinj).1 = t ∘ Tuple.sort t := rfl

theorem ointer_le_inter_osort {n : ℕ} (t : K.OIdx n) (hinj : Function.Injective t) :
    K.ointer t ≤ K.inter (K.osort t hinj) :=
  le_iInf fun j => iInf_le _ (Tuple.sort t j)

theorem inter_osort_le_ointer {n : ℕ} (t : K.OIdx n) (hinj : Function.Injective t) :
    K.inter (K.osort t hinj) ≤ K.ointer t :=
  le_iInf fun j => (iInf_le _ ((Tuple.sort t).symm j)).trans (by
    change K.U (t (Tuple.sort t ((Tuple.sort t).symm j))) ≤ K.U (t j)
    rw [Equiv.apply_symm_apply])

theorem ointer_le_preimage_ointer_comp {X Y : Scheme.{u}} (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover)
    (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    {n : ℕ} (t : 𝒲.OIdx n) : 𝒲.ointer t ≤ h ⁻¹ᵁ 𝒦.ointer (lam ∘ t) := by
  change 𝒲.ointer t ≤ h ⁻¹ᵁ (⨅ j, 𝒦.U (lam (t j)))
  rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
  exact le_iInf fun j => (iInf_le (fun i => 𝒲.U (t i)) j).trans (hlam _)

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

abbrev ocochain (n : ℕ) : Type u := ∀ t : K.OIdx n, F.obj (K.ointer t)

def od (n : ℕ) : F.ocochain K n →ₗ[R] F.ocochain K (n + 1) :=
  LinearMap.pi fun t => ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((F.res (K.ointer_le_ointer_oface t j)).comp (LinearMap.proj (K.oface t j)))

theorem od_apply (n : ℕ) (c : F.ocochain K n) (t : K.OIdx (n + 1)) :
    F.od K n c t = ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • F.res (K.ointer_le_ointer_oface t j) (c (K.oface t j)) := by
  simp only [od, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

def ocup (a b n : ℕ) (h : a + b = n) (α : (unit π).ocochain K a) (β : F.ocochain K b) : F.ocochain K n :=
  fun t => (V.presheaf.map (homOfLE (K.ointer_le_ointer_ofrontFace a b n h t)).op).hom (α (K.ofrontFace a b n h t))
    • F.res (K.ointer_le_ointer_obackFace a b n h t) (β (K.obackFace a b n h t))

theorem ocup_apply (a b n : ℕ) (h : a + b = n) (α : (unit π).ocochain K a) (β : F.ocochain K b) (t : K.OIdx n) :
    F.ocup K a b n h α β t =
      (V.presheaf.map (homOfLE (K.ointer_le_ointer_ofrontFace a b n h t)).op).hom (α (K.ofrontFace a b n h t))
        • F.res (K.ointer_le_ointer_obackFace a b n h t) (β (K.obackFace a b n h t)) :=
  rfl

def ores (n : ℕ) : F.ocochain K n →ₗ[R] F.cochain K n :=
  LinearMap.pi fun s => LinearMap.proj (R := R) (φ := fun t : K.OIdx n => F.obj (K.ointer t)) s.1

theorem ores_apply (n : ℕ) (c : F.ocochain K n) (s : K.Idx n) : F.ores K n c s = c s.1 := rfl

def oext (n : ℕ) : F.cochain K n →ₗ[R] F.ocochain K n :=
  LinearMap.pi fun t => by
    classical
    exact if hinj : Function.Injective t then
      ((Equiv.Perm.sign (Tuple.sort t) : ℤˣ) : ℤ) •
        ((F.res (K.ointer_le_inter_osort t hinj)).comp (LinearMap.proj (K.osort t hinj)))
    else 0

theorem oext_apply_of_injective (n : ℕ) (z : F.cochain K n) (t : K.OIdx n) (hinj : Function.Injective t) :
    F.oext K n z t = ((Equiv.Perm.sign (Tuple.sort t) : ℤˣ) : ℤ) •
      F.res (K.ointer_le_inter_osort t hinj) (z (K.osort t hinj)) := by
  classical
  simp only [oext, LinearMap.pi_apply, dif_pos hinj, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

theorem oext_apply_of_not_injective (n : ℕ) (z : F.cochain K n) (t : K.OIdx n) (hinj : ¬ Function.Injective t) :
    F.oext K n z t = 0 := by
  classical
  simp only [oext, LinearMap.pi_apply, dif_neg hinj, LinearMap.zero_apply]

variable {R' : Type u} [CommRing R'] {X Y : Scheme.{u}} {πX : X ⟶ Spec (.of R')} {πY : Y ⟶ Spec (.of R)}

def ounitPullback (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (c : (unit πY).ocochain 𝒦 n) : (unit πX).ocochain 𝒲 n :=
  fun t => (X.presheaf.map (homOfLE (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam t)).op).hom
    ((h.app (𝒦.ointer (lam ∘ t))).hom (c (lam ∘ t)))

theorem ounitPullback_apply (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ)
    (c : (unit πY).ocochain 𝒦 n) (t : 𝒲.OIdx n) :
    ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n c t =
      (X.presheaf.map (homOfLE (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam t)).op).hom
        ((h.app (𝒦.ointer (lam ∘ t))).hom (c (lam ∘ t))) :=
  rfl

end OModulePresheaf

end AlgebraicGeometry

end


