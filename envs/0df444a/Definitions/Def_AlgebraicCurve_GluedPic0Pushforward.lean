-- Prove2me | Definitions.Def_AlgebraicCurve_GluedPic0Pushforward
-- name    : AlgebraicCurve_GluedPic0Pushforward
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/8d9aec5b-d61c-5009-a279-de4474c435c2
-- title:
--   Pushforward maps on glued degree-zero Picard groups
-- statement:
--   Fix a base field $K$ and two $K$-algebras $F$, $F'$ that are fields, a $K$-algebra map $\varphi : F \to F'$ whose underlying ring map is integral, finite sets $S' \subseteq \mathrm{Place}(F'/K)^2$ and $S \subseteq \mathrm{Place}(F/K)^2$ of node data, a map $\nu : S' \to S$ and multiplicities $m : S' \to \mathbb{N}$. Recall that a gluing datum for $S$ is a triple consisting of two divisors on $F/K$ together with a function $S \to \mathrm{Additive}(K^{\times})$; it is admissible when both divisors have degree zero and, for every $s \in S$, the first divisor vanishes at $s_1$ and the second at $s_2$; and $\mathrm{GluedPic0}$ is the quotient of the admissible subgroup by its intersection with the glued principal data.
--
--   The module defines, first, `nodeFibreSum`, the additive map sending $w : S' \to \mathrm{Additive}(K^{\times})$ to $n \mapsto \sum_{\nu n' = n} m(n') \cdot w(n')$ (multiplicatively, the product of the $m(n')$-th powers over the nodes of $S'$ in the fibre). Next, `GluingData.pushforwardMap` is the additive map on gluing data which applies `Divisor.pushforwardAlong φ hφ` to each of the two divisors and `nodeFibreSum` to the node function. Two lemmas are proved: a pushforward divisor vanishes at a place $v$ of $F$ as soon as the original vanishes at every place of $F'$ restricting to $v$; and `pushforwardMap_mem_admissible`, which shows admissibility is preserved provided $S'$ is complete above $S$, i.e. every place of $F'$ restricting to $n_1$ (resp. $n_2$) for $n \in S$ occurs as the first (resp. second) component of some node of $S'$. Finally, given as explicit hypotheses that admissible data map to admissible data and that glued principal data map to glued principal data, `GluedPic0.pushforwardMap` is the induced homomorphism $\mathrm{GluedPic0}(F',S') \to \mathrm{GluedPic0}(F,S)$, computed on classes by the restricted map, and shown to carry the node-unit homomorphism of $S'$ to that of $S$ composed with `nodeFibreSum`. The transport of principality is taken as a hypothesis, not proved here.
--
--   **Relation to Mathlib.** Mathlib has no notion of gluing data for a nodal curve or of the associated glued degree-zero Picard group; these, together with the project's `Place`, `Divisor` and `Divisor.pushforwardAlong` along an integral $K$-algebra map, are the project's own, built on Mathlib's `Finsupp`, `ValuationSubring` and quotient-group machinery.
--
--   **Where it is used.** The intended application is to degeneracy coverings of special fibres of modular curves, where $S$ and $S'$ record the nodes (pairs of a place and its Frobenius translate), $\nu$ is restriction of places and $m$ combines ramification index and inertia degree; the resulting pushforward on glued Picard groups supplies the maps on component and character groups used in the level-change arguments for mod $\ell$ Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_GluedPic0Pushforward.lean

import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

section PushforwardAlong

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

namespace GluingData

variable (S' : Finset (Place K F' × Place K F')) (S : Finset (Place K F × Place K F))
variable [DecidableEq ↥S] (ν : ↥S' → ↥S) (m : ↥S' → ℕ)

def nodeFibreSum : (↥S' → Additive Kˣ) →+ (↥S → Additive Kˣ) :=
  AddMonoidHom.mk' (fun w n => ∑ n' with ν n' = n, m n' • w n') (fun w w' => by
    funext n
    rw [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n' _ => smul_add (m n') (w n') (w' n'))

@[simp]
theorem nodeFibreSum_apply (w : ↥S' → Additive Kˣ) (n : ↥S) :
    nodeFibreSum S' S ν m w n = ∑ n' with ν n' = n, m n' • w n' :=
  rfl

variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

def pushforwardMap : GluingData K F' S' →+ GluingData K F S :=
  AddMonoidHom.mk'
    (fun x => (Divisor.pushforwardAlong φ hφ x.1, Divisor.pushforwardAlong φ hφ x.2.1,
      nodeFibreSum S' S ν m x.2.2))
    (fun x y => by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp
      · simp
      · simp)

@[simp]
theorem pushforwardMap_apply (x : GluingData K F' S') :
    pushforwardMap S' S ν m φ hφ x
      = (Divisor.pushforwardAlong φ hφ x.1, Divisor.pushforwardAlong φ hφ x.2.1,
          nodeFibreSum S' S ν m x.2.2) :=
  rfl

theorem _root_.AlgebraicCurve.Divisor.pushforwardAlong_apply_eq_zero (D : Divisor K F')
    (v : Place K F) (h : ∀ w : Place K F', w.restrictAlong φ hφ = v → D w = 0) :
    Divisor.pushforwardAlong φ hφ D v = 0 := by
  classical
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  show Divisor.pushforward F D v = 0
  rw [Divisor.pushforward_apply]
  refine Finset.sum_eq_zero fun w _ => ?_
  split_ifs with hwv
  · rw [h w hwv, zero_mul]
  · rfl

theorem pushforwardMap_mem_admissible
    (hcov₁ : ∀ n ∈ S, ∀ w : Place K F', w.restrictAlong φ hφ = n.1 → ∃ n' ∈ S', n'.1 = w)
    (hcov₂ : ∀ n ∈ S, ∀ w : Place K F', w.restrictAlong φ hφ = n.2 → ∃ n' ∈ S', n'.2 = w)
    {x : GluingData K F' S'} (hx : x ∈ admissible S') :
    pushforwardMap S' S ν m φ hφ x ∈ admissible S := by
  obtain ⟨h₁, h₂, hav⟩ := hx
  refine ⟨Divisor.pushforwardAlong_mem_degZero φ hφ h₁,
    Divisor.pushforwardAlong_mem_degZero φ hφ h₂, fun n hn => ⟨?_, ?_⟩⟩
  · refine Divisor.pushforwardAlong_apply_eq_zero φ hφ x.1 n.1 fun w hw => ?_
    obtain ⟨n', hn', rfl⟩ := hcov₁ n hn w hw
    exact (hav n' hn').1
  · refine Divisor.pushforwardAlong_apply_eq_zero φ hφ x.2.1 n.2 fun w hw => ?_
    obtain ⟨n', hn', rfl⟩ := hcov₂ n hn w hw
    exact (hav n' hn').2

end GluingData

namespace GluedPic0

variable (S' : Finset (Place K F' × Place K F')) (S : Finset (Place K F × Place K F))
variable [DecidableEq ↥S] (ν : ↥S' → ↥S) (m : ↥S' → ℕ)
variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

def admissiblePushforwardMap
    (hadm : ∀ x ∈ GluingData.admissible S',
      GluingData.pushforwardMap S' S ν m φ hφ x ∈ GluingData.admissible S) :
    ↥(GluingData.admissible S') →+ ↥(GluingData.admissible S) :=
  ((GluingData.pushforwardMap S' S ν m φ hφ).domRestrict (GluingData.admissible S')).codRestrict _
    (fun x => hadm x x.2)

@[simp]
theorem coe_admissiblePushforwardMap
    (hadm : ∀ x ∈ GluingData.admissible S',
      GluingData.pushforwardMap S' S ν m φ hφ x ∈ GluingData.admissible S)
    (x : ↥(GluingData.admissible S')) :
    (admissiblePushforwardMap S' S ν m φ hφ hadm x : GluingData K F S)
      = GluingData.pushforwardMap S' S ν m φ hφ (x : GluingData K F' S') :=
  rfl

def pushforwardMap
    (hadm : ∀ x ∈ GluingData.admissible S',
      GluingData.pushforwardMap S' S ν m φ hφ x ∈ GluingData.admissible S)
    (hprin : ∀ x : GluingData K F' S', GluingData.IsGluedPrincipal S' x →
      GluingData.IsGluedPrincipal S (GluingData.pushforwardMap S' S ν m φ hφ x)) :
    GluedPic0 K F' S' →+ GluedPic0 K F S :=
  QuotientAddGroup.map _ _ (admissiblePushforwardMap S' S ν m φ hφ hadm) (by
    rintro x hx
    simp only [AddSubgroup.mem_addSubgroupOf] at hx ⊢
    exact hprin _ hx)

@[simp]
theorem pushforwardMap_mk
    (hadm : ∀ x ∈ GluingData.admissible S',
      GluingData.pushforwardMap S' S ν m φ hφ x ∈ GluingData.admissible S)
    (hprin : ∀ x : GluingData K F' S', GluingData.IsGluedPrincipal S' x →
      GluingData.IsGluedPrincipal S (GluingData.pushforwardMap S' S ν m φ hφ x))
    (x : ↥(GluingData.admissible S')) :
    pushforwardMap S' S ν m φ hφ hadm hprin (mk S' x)
      = mk S (admissiblePushforwardMap S' S ν m φ hφ hadm x) :=
  rfl

theorem pushforwardMap_nodeUnit
    (hadm : ∀ x ∈ GluingData.admissible S',
      GluingData.pushforwardMap S' S ν m φ hφ x ∈ GluingData.admissible S)
    (hprin : ∀ x : GluingData K F' S', GluingData.IsGluedPrincipal S' x →
      GluingData.IsGluedPrincipal S (GluingData.pushforwardMap S' S ν m φ hφ x))
    (w : ↥S' → Additive Kˣ) :
    pushforwardMap S' S ν m φ hφ hadm hprin (nodeUnit S' w)
      = nodeUnit S (GluingData.nodeFibreSum S' S ν m w) := by
  rw [nodeUnit_apply, nodeUnit_apply, pushforwardMap_mk]
  refine congrArg (mk S) (Subtype.ext ?_)
  rw [coe_admissiblePushforwardMap]
  exact Prod.ext (map_zero _) (Prod.ext (map_zero _) rfl)

end GluedPic0

end PushforwardAlong

end AlgebraicCurve

end


