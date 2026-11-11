-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Rigidification
-- name    : SymmetricDepthHierarchy_ConstantDepth_Rigidification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:29.829585+00:00
-- url     : https://prove2.me/theorems/7d55925c-499e-472d-aeb4-206d89b26bfb
-- title:
--   The rigidification of a circuit; support size and support depth of arbitrary circuits
-- statement:
--   Let $C$ be a circuit and write $m(g,h)$ for the multiplicity of the wire from $h$ to $g$. The equivalence $\equiv$ on gates is defined by induction on the height: input gates are equivalent iff they have the same label; gates $g,g'$ are equivalent iff they have the same height and label and
--   $$m(g,c):=\sum_{h\in c}m(g,h)=m(g',c)$$
--   for every class $c$ of gates of smaller height. The **rigidification** $C'$ has as gates the classes from which the class $[\mathrm{out}]$ of the output gate can be reached; the class $[g]$ carries the label of $g$ and has a wire of multiplicity $m(g,c)$ from every class $c$ (proof of Lemma 2.4).
--
--   For an arbitrary matrix-symmetric circuit, the **support size** and **support depth** are those of its rigidification.
--
--   This fixes the support depth of every circuit in the lower bounds (Corollary B.23, Theorem 3.1).
--
--   **Formalization Note.** The classes are finite sets of gates; the label and the outgoing multiplicities of a class are read off a chosen representative (all members agree). Heights are longest downward paths, which coincide with the source's heights when every internal gate has a child.
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), Appendix A, proof of Lemma 2.4, p. 27 (PDF p. 30); §2.3, p. 8 (PDF p. 11)

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Circuit
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Support

open scoped Classical

noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth

/-!
# The rigidification of a circuit; support size and support depth of arbitrary circuits

STOC 2027 submission #1521, proof of Lemma 2.4 (Appendix A, printed p. 27, PDF p. 30) and §2.3
(printed p. 8, PDF p. 11): "For an arbitrary matrix-symmetric circuit, we define its support size
and support depth as those of its rigidification."

The equivalence `≡` on gates is defined by induction on the height. Input gates are equivalent
iff they have the same label. Gates `g, g'` of height `k` are equivalent iff they have the same
label and `m(g, c) = m(g', c)` for every class `c` of gates of smaller height, where
`m(g, c) = ∑_{h ∈ c} m(g, h)`. The rigidification has as gates the classes from which the class
of the output gate can be reached; the class `[g]` carries the label of `g` and has a wire of
multiplicity `m(g, c)` from every class `c`.
-/

namespace Circuit

variable {K : Type} [Field K] {n : ℕ} {V : Type} [Fintype V]

/-- `eqvAt C k g g'`: the gates `g` and `g'` both have height `k` and are equivalent. -/
def eqvAt (C : Circuit K n V) : ℕ → V → V → Prop
  | k, g, g' => C.label g = C.label g' ∧ C.height g = k ∧ C.height g' = k ∧
      ∀ j, (hj : j < k) → ∀ h₀ : V, C.height h₀ = j →
        (∑ h ∈ Finset.univ.filter (fun h => C.eqvAt j h h₀), C.mult g h) =
        (∑ h ∈ Finset.univ.filter (fun h => C.eqvAt j h h₀), C.mult g' h)
termination_by k => k

/-- The equivalence `g ≡ g'` of the proof of Lemma 2.4. -/
def GateEquiv (C : Circuit K n V) (g g' : V) : Prop := C.eqvAt (C.height g) g g'

/-- The equivalence class `[g]`. -/
def classOf (C : Circuit K n V) (g : V) : Finset V := Finset.univ.filter (C.GateEquiv g)

/-- `c` is an equivalence class. -/
def IsClass (C : Circuit K n V) (c : Finset V) : Prop := ∃ g, c = C.classOf g

/-- A representative of a (nonempty) class. -/
def rep (C : Circuit K n V) (c : Finset V) : V :=
  if h : c.Nonempty then h.choose else C.out

/-- The multiplicity `m(g, c) = ∑_{h ∈ c} m(g, h)` of the wire from the class `d` into the
class `c`, computed at the representative of `c`. -/
def classMult (C : Circuit K n V) (c d : Finset V) : ℕ := ∑ h ∈ d, C.mult (C.rep c) h

/-- Wires between classes. -/
def ClassWire (C : Circuit K n V) (d c : Finset V) : Prop :=
  C.IsClass d ∧ C.IsClass c ∧ 0 < C.classMult c d

/-- The gates of the rigidification: the classes from which `[out]` can be reached. -/
def RGate (C : Circuit K n V) : Type :=
  {c : Finset V // C.IsClass c ∧ Relation.ReflTransGen C.ClassWire c (C.classOf C.out)}

instance (C : Circuit K n V) : Fintype C.RGate := by
  unfold RGate; infer_instance

instance (C : Circuit K n V) : DecidableEq C.RGate := by
  unfold RGate; infer_instance

/-- The rigidification `C′` of `C` (proof of Lemma 2.4). -/
def rigidification (C : Circuit K n V) : Circuit K n C.RGate where
  label c := C.label (C.rep c.1)
  mult c d := C.classMult c.1 d.1
  out := ⟨C.classOf C.out, ⟨C.out, rfl⟩, Relation.ReflTransGen.refl⟩

/-- The support size of an arbitrary circuit: that of its rigidification. -/
def supportSize (C : Circuit K n V) : ℕ := C.rigidification.maxSup

/-- The support depth of an arbitrary circuit: that of its rigidification. -/
def supportDepth (C : Circuit K n V) : ℕ := C.rigidification.rigidSupportDepth

end Circuit

end SymmetricDepthHierarchy.ConstantDepth


