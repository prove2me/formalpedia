-- Prove2me | Definitions.Def_RelativisticZK205_ThreeCol_Supplement_Field
-- name    : RelativisticZK205_ThreeCol_Supplement_Field
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:31:38.696788+00:00
-- url     : https://prove2.me/theorems/ca517381-1263-42e8-8796-a39096dfd6fd
-- title:
--   Arbitrary characteristic-two fields and the Γ_LHV interfaces
-- statement:
--   Let $F$ be a finite field and choose additive coordinates
--   $$e:F\simeq (\mathbb Z/2\mathbb Z)^\ell.$$
--   Such coordinates express a choice of $\mathbb F_2$ basis, imply characteristic two and cardinality $2^\ell$, and identify addition with bitwise XOR. Since committed entries are Boolean, multiplication by them is either zero or the identity. There is no restriction to the two-element field.
--
--   The real field device samples uniform $\Pi$ and a uniform full matrix $A\in F^{n\times n}$ directly, and computes
--   $$Y_{ij}=(D_{ij}:F)X_{ij}+A_{ij}.$$
--   Its two challenge replies have the same finite, restricted payloads as the bit device. The simulated field device encodes Alice's field input into bits, runs the actual PR simulator, and decodes only the exposed outputs. Lexicographic cycle serialization is specified also for field values. This connects the exact field protocol to its bitwise nonlocal implementation without assuming any simulation property.
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.12, §5.2, Protocol Γ_LHV and simulators; p.13, proof of Theorem 2

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Supplement_Protocol

namespace RelativisticZK205.ThreeCol.Supplement

/-- Coordinates in any F₂ basis, expressed as an additive equivalence. For a
field this implies characteristic two and exactly 2^ℓ elements. Additivity is
also F₂-linearity: scalars are only zero and one. -/
abbrev Coordinates (F : Type) [Field F] (ℓ : ℕ) := F ≃+ (Fin ℓ → ZMod 2)
abbrev FieldMatrix (F : Type) (n : ℕ) := Position n → F

noncomputable def toBits {F : Type} [Field F] {ℓ : ℕ} (e : Coordinates F ℓ)
    (x : F) : Word ℓ := fun t => decide (e x t = 1)

noncomputable def fromBits {F : Type} [Field F] {ℓ : ℕ} (e : Coordinates F ℓ)
    (b : Word ℓ) : F := e.symm (fun t => if b t then 1 else 0)

inductive FieldOpening (F : Type) (n : ℕ) where
  | graph : Equiv.Perm (Vertex n) → BooleanMatrix n → FieldMatrix F n → FieldOpening F n
  | cycle : (K : EdgeSet n) → (K → F) → FieldOpening F n
  deriving Fintype

noncomputable def fieldCycleOpening {F : Type} {n : ℕ} (C : EdgeSet n)
    (A : FieldMatrix F n) : FieldOpening F n :=
  .cycle C (fun i => A i.1)

noncomputable def decodeOpening {F : Type} [Field F] {n ℓ : ℕ}
    (e : Coordinates F ℓ) (r : Opening n ℓ) : FieldOpening F n :=
  match r with
  | .graph p D A => .graph p D (fun i => fromBits e (A i))
  | .cycle K A => .cycle K (fun i => fromBits e (A i))

/-- The field-valued cycle payload has the same fixed wire order as the bits. -/
noncomputable def fieldCycleSerialization {F : Type} {n : ℕ} (C : EdgeSet n) (A : C → F) :
    List (Position n × F) :=
  (C.attach.toList.mergeSort (fun i j =>
    i.1.1.val * n + i.1.2.val ≤ j.1.1.val * n + j.1.2.val)).map (fun i => (i.1, A i))

/-- The actual field-arithmetic honest strategy: uniform shared permutation
and independent uniform masks; every ordered entry, including the diagonal. -/
noncomputable def realFieldDevice {F : Type} [Field F] [Fintype F] {n : ℕ}
    (G : SimpleGraph (Vertex n)) (C : EdgeSet n) :
    Device (Option (FieldMatrix F n)) BobQuery
      (Option (FieldMatrix F n)) (Option (FieldOpening F n)) where
  State := Equiv.Perm (Vertex n) × FieldMatrix F n
  initial := (PMF.uniformOfFintype (Equiv.Perm (Vertex n))).bind fun p =>
    (PMF.uniformOfFintype (FieldMatrix F n)).map fun A => (p,A)
  alice s q := PMF.pure (q.map (fun X => fun i =>
    (if adjacency G s.1 i then (1 : F) else 0) * X i + s.2 i), s)
  bob s q := PMF.pure (q.map (fun c => if c then fieldCycleOpening (relabelCycle s.1 C) s.2
    else FieldOpening.graph s.1 (adjacency G s.1) s.2), s)

/-- The very same explicit PR simulator transported through the chosen field
coordinates. In particular this device has no C argument. -/
noncomputable def simFieldDevice {F : Type} [Field F] {n ℓ : ℕ}
    (G : SimpleGraph (Vertex n)) (e : Coordinates F ℓ) :
    Device (Option (FieldMatrix F n)) BobQuery
      (Option (FieldMatrix F n)) (Option (FieldOpening F n)) where
  State := (simDevice G ℓ).State
  initial := (simDevice G ℓ).initial
  alice s q := ((simDevice G ℓ).alice s (q.map (fun X i => toBits e (X i)))).map
    fun ys => (ys.1.map (fun Y i => fromBits e (Y i)), ys.2)
  bob s q := ((simDevice G ℓ).bob s q).map
    fun r => (r.1.map (decodeOpening e), r.2)

end RelativisticZK205.ThreeCol.Supplement


