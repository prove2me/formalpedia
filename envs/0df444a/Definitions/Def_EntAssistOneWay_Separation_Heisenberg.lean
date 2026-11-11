-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_Heisenberg
-- name    : EntAssistOneWay_Separation_Heisenberg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:03.403209+00:00
-- url     : https://prove2.me/theorems/2a4aac51-f931-42e0-a420-f7ba382849ca
-- title:
--   Generalized Heisenberg groups over the three-element field
-- statement:
--   The group $H_m(\mathbb F_3)$ consists of triples $(u,v,w)$ with $u,v\in\mathbb F_3^m$ and $w\in\mathbb F_3$. Its multiplication, inverse, and central generator are
--   $$(u,v,w)(u',v',w')=(u+u',v+v',w+w'+u\cdot v'),\quad (u,v,w)^{-1}=(-u,-v,-w+u\cdot v),\quad\zeta=(0,0,1).$$
--   The group family used in the separation is $G_r=H_{2^{2r}}(\mathbb F_3)$.
--
--   The finite carrier and actual group operations are defined explicitly. Associativity and inverse laws in the group instance are structural proofs; no representation-theoretic claim is built into the definition.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), pp. 37–38, proof of Theorem 6.1, generalized Heisenberg group and choice of m

import Definitions.Def_EntAssistOneWay_Separation_GroupProblems

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- The generalized Heisenberg group over F₃ (p. 37). -/
@[ext] structure Heisenberg (m : ℕ) where
  u : Fin m → ZMod 3
  v : Fin m → ZMod 3
  w : ZMod 3
  deriving DecidableEq, Fintype

instance heisenbergGroup (m : ℕ) : Group (Heisenberg m) where
  mul a b := ⟨a.u + b.u, a.v + b.v, a.w + b.w + ∑ i, a.u i * b.v i⟩
  one := ⟨0, 0, 0⟩
  inv a := ⟨-a.u, -a.v, -a.w + ∑ i, a.u i * a.v i⟩
  mul_assoc a b c := by
    change Heisenberg.mk ((a.u + b.u) + c.u) ((a.v + b.v) + c.v)
      ((a.w + b.w + ∑ i, a.u i * b.v i) + c.w + ∑ i, (a.u + b.u) i * c.v i) =
      Heisenberg.mk (a.u + (b.u + c.u)) (a.v + (b.v + c.v))
      (a.w + (b.w + c.w + ∑ i, b.u i * c.v i) + ∑ i, a.u i * (b.v + c.v) i)
    congr 1
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
    · simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
      ring
  one_mul a := by
    change Heisenberg.mk (0 + a.u) (0 + a.v) (0 + a.w + ∑ i, (0 : Fin m → ZMod 3) i * a.v i) = a
    simp
  mul_one a := by
    change Heisenberg.mk (a.u + 0) (a.v + 0) (a.w + 0 + ∑ i, a.u i * (0 : Fin m → ZMod 3) i) = a
    simp
  inv_mul_cancel a := by
    change Heisenberg.mk (-a.u + a.u) (-a.v + a.v)
      ((-a.w + ∑ i, a.u i * a.v i) + a.w + ∑ i, (-a.u) i * a.v i) = Heisenberg.mk 0 0 0
    simp [Finset.sum_neg_distrib]

/-- Distinguished central element ζ = (0,0,1). -/
def heisenbergZeta (m : ℕ) : Heisenberg m := ⟨0, 0, 1⟩

/-- The explicit group family in Theorem 6.1. -/
abbrev SeparationGroup (r : ℕ) := Heisenberg (2 ^ (2 * r))

end

end EntAssistOneWay.Separation


