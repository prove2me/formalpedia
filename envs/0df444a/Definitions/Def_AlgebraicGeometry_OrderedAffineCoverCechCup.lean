-- Prove2me | Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
-- name    : AlgebraicGeometry_OrderedAffineCoverCechCup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/d4cb97ef-c848-53d9-846d-e326a20e2f04
-- title:
--   Front and back faces; cup product on Čech cochains
-- statement:
--   The setting is a scheme $V$ together with an ordered affine cover $K$, i.e. a finite linearly ordered index type $\iota$ and affine opens $U_i$ with $\bigsqcup$-supremum $\top$; an index of degree $n$ is a strictly monotone map $s : \mathrm{Fin}(n+1) \to \iota$, with associated open $K.\mathrm{inter}\,s = \bigsqcap_j U_{s(j)}$. For natural numbers $a, b, n$ with $h : a + b = n$ and $s$ of degree $n$, `frontFace` is the degree-$a$ index $j \mapsto s(j)$ given by the first $a+1$ entries $(s_0 < \dots < s_a)$, and `backFace` is the degree-$b$ index $j \mapsto s(a+j)$ given by the last $b+1$ entries $(s_a < \dots < s_n)$; strict monotonicity of each is inherited from that of $s$, and the two faces share the vertex $s_a$. The lemmas `frontFace_apply` and `backFace_apply` record these formulas for the underlying maps, and `inter_le_inter_frontFace`, `inter_le_inter_backFace` record the inclusions $K.\mathrm{inter}\,s \le K.\mathrm{inter}$ of each face.
--
--   For a commutative ring $R$, a morphism $\pi : V \to \operatorname{Spec} R$ and a module-presheaf datum $F$ over $\pi$ (a family $F.\mathrm{obj}\,U$ of $R$-modules, each also a module over $\Gamma(V,U)$ compatibly, with restriction maps), `cup` takes $a, b, n$ with $a+b=n$, a degree-$a$ cochain $\alpha$ of the structure-sheaf datum `unit π` (so $\alpha(t) \in \Gamma(V, K.\mathrm{inter}\,t)$) and a degree-$b$ cochain $\beta$ of $F$, and returns the degree-$n$ cochain of $F$ whose value at $s$ is
--   $$\bigl(\alpha(\mathrm{frontFace}\,s)\bigr)\big|_{K.\mathrm{inter}\,s} \cdot \bigl(\beta(\mathrm{backFace}\,s)\bigr)\big|_{K.\mathrm{inter}\,s},$$
--   the first factor restricted by the structure presheaf of $V$, the second by the restriction maps of $F$, and the product being the $\Gamma(V, K.\mathrm{inter}\,s)$-action on $F.\mathrm{obj}(K.\mathrm{inter}\,s)$. The lemma `cup_apply` states this formula. The target degree $n$ and the equation $a+b=n$ are explicit arguments, so that the value lies in a single fixed cochain module. The module defines the product only; no Leibniz rule, associativity, unitality or passage to cohomology is asserted here.
--
--   **Relation to Mathlib.** Mathlib has no cup product on Čech cochains of an ordered affine cover of a scheme; the face operators and the product here are the project's own, defined on top of the project's `Scheme.OrderedAffineCover` and `OModulePresheaf` and their `cochain` complexes.
--
--   **Where it is used.** These are vocabulary for the project's Čech-complex treatment of module presheaves on a scheme over $\operatorname{Spec} R$, which supplies the cohomology and base-change input used in the geometric part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCechCup.lean

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

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

def frontFace (a b n : ℕ) (h : a + b = n) (s : K.Idx n) : K.Idx a :=
  ⟨fun j => s.1 ⟨j.1, by omega⟩, fun _ _ hj => s.2 (Fin.mk_lt_mk.2 (Fin.lt_def.1 hj))⟩

def backFace (a b n : ℕ) (h : a + b = n) (s : K.Idx n) : K.Idx b :=
  ⟨fun j => s.1 ⟨a + j.1, by omega⟩, fun _ _ hj => s.2 (Fin.mk_lt_mk.2 (by have := Fin.lt_def.1 hj; omega))⟩

theorem frontFace_apply (a b n : ℕ) (h : a + b = n) (s : K.Idx n) (j : Fin (a + 1)) :
    (K.frontFace a b n h s).1 j = s.1 ⟨j.1, by omega⟩ :=
  rfl

theorem backFace_apply (a b n : ℕ) (h : a + b = n) (s : K.Idx n) (j : Fin (b + 1)) :
    (K.backFace a b n h s).1 j = s.1 ⟨a + j.1, by omega⟩ :=
  rfl

theorem inter_le_inter_frontFace (a b n : ℕ) (h : a + b = n) (s : K.Idx n) :
    K.inter s ≤ K.inter (K.frontFace a b n h s) :=
  le_iInf fun _ => iInf_le _ _

theorem inter_le_inter_backFace (a b n : ℕ) (h : a + b = n) (s : K.Idx n) :
    K.inter s ≤ K.inter (K.backFace a b n h s) :=
  le_iInf fun _ => iInf_le _ _

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

def cup (a b n : ℕ) (h : a + b = n) (α : (unit π).cochain K a) (β : F.cochain K b) : F.cochain K n :=
  fun s => (V.presheaf.map (homOfLE (K.inter_le_inter_frontFace a b n h s)).op).hom (α (K.frontFace a b n h s))
    • F.res (K.inter_le_inter_backFace a b n h s) (β (K.backFace a b n h s))

theorem cup_apply (a b n : ℕ) (h : a + b = n) (α : (unit π).cochain K a) (β : F.cochain K b) (s : K.Idx n) :
    F.cup K a b n h α β s =
      (V.presheaf.map (homOfLE (K.inter_le_inter_frontFace a b n h s)).op).hom (α (K.frontFace a b n h s))
        • F.res (K.inter_le_inter_backFace a b n h s) (β (K.backFace a b n h s)) :=
  rfl

end OModulePresheaf

end AlgebraicGeometry

end


