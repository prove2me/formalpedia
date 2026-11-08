-- Prove2me | Definitions.Def_FRouting_Circuit
-- name    : FRouting_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:53.421195+00:00
-- url     : https://prove2.me/theorems/13229f31-9872-40f7-8094-975ee5695fd9
-- title:
--   Circuits with ancillas and discarded wires
-- statement:
--   A **circuit** over dimension $d$ from $\mathrm{in}$ input wires to $\mathrm{out}$ kept wires has a number of ancillas, each starting in $|0\rangle$, a list of gates on all the wires, and an injective choice of the kept wires. Its **channel** appends the ancillas, applies the gates and traces out the wires not kept; its **output state** is that channel on the all-zero state. The size is the number of gates and the width is the number of wires.
--
--   Every circuit gives a real channel: completeness of the Kraus family is proved from the unitarity of the gates.
--
--   **Formalization Note** The paper calls the printed object both "a quantum channel" and "the circuit" of size and width at most $T(n)$ (p.4). Mid-circuit measurement is covered by purification, the paper's convention (footnotes 1, 3).
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 1.2, p.4; Definition 5.5, p.21

import Definitions.Def_FRouting_Gate
import Definitions.Def_WildeQIT_QChannel

set_option autoImplicit false

open Matrix

namespace FRouting

open WildeQIT

/-- **A quantum circuit on qudits of dimension `d`**, from `inW` input wires to `outW` kept wires.
Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), p.4,
calls the object both "a quantum channel" and "the circuit printed by each generator", of "size at
most T(n)", acting on "that many qubits". This structure is that reading: the input wires come first,
then `ancillas` wires in `|0⟩`; the gates act on all of them; the wires in `kept` form the output, in
that order, and the others are traced out.

**Formalization Note** Mid-circuit measurement is covered by purification, the paper's convention
(its footnotes 1, 3). `d_pos` makes `|0⟩` exist. -/
structure Circuit (d inW outW : ℕ) where
  d_pos : 0 < d
  /-- The number of ancilla wires, each starting in `|0⟩`. -/
  ancillas : ℕ
  /-- The gates, first applied first. -/
  gates : List (Gate d (inW + ancillas))
  /-- The output wires. -/
  kept : Fin outW → Fin (inW + ancillas)
  kept_inj : Function.Injective kept

namespace Circuit

variable {d inW outW : ℕ} (C : Circuit d inW outW)

/-- The number of wires of the circuit. -/
def width : ℕ := inW + C.ancillas

/-- The number of gates of the circuit. -/
def size : ℕ := C.gates.length

/-- The unitary `g_m ⋯ g₁` of the gate list `g₁, …, g_m`. -/
noncomputable def unitary :
    Matrix (Fin (inW + C.ancillas) → Fin d) (Fin (inW + C.ancillas) → Fin d) ℂ :=
  C.gates.foldl (fun U g => g.matrix * U) 1

/-- The basis state `|s⟩|0…0⟩` of all wires, for an input basis state `s`. -/
def prep (s : Fin inW → Fin d) : Fin (inW + C.ancillas) → Fin d :=
  Fin.append s fun _ => ⟨0, C.d_pos⟩

open scoped Classical in
/-- The wires that are traced out. -/
abbrev Traced : Type := { w : Fin (inW + C.ancillas) // w ∉ Set.range C.kept }

open scoped Classical in
/-- A basis state of all the wires is a basis state of the kept wires and one of the traced wires:
`(split.symm (o, e)) (kept i) = o i`, and `split.symm (o, e)` is `e` on the traced wires. -/
noncomputable def split :
    (Fin (inW + C.ancillas) → Fin d) ≃ (Fin outW → Fin d) × (C.Traced → Fin d) :=
  (Equiv.piEquivPiSubtypeProd (· ∈ Set.range C.kept) fun _ => Fin d).trans
    (Equiv.prodCongr
      (Equiv.arrowCongr (Equiv.ofInjective C.kept C.kept_inj).symm (Equiv.refl _))
      (Equiv.refl _))

theorem unitary_unitary : C.unitaryᴴ * C.unitary = 1 := by
  have key : ∀ (l : List (Gate d (inW + C.ancillas)))
      (U : Matrix (Fin (inW + C.ancillas) → Fin d) (Fin (inW + C.ancillas) → Fin d) ℂ),
      Uᴴ * U = 1 → (l.foldl (fun U g => g.matrix * U) U)ᴴ * l.foldl (fun U g => g.matrix * U) U = 1 := by
    intro l
    induction l with
    | nil => intro U h; simpa using h
    | cons g l ih =>
      intro U h
      refine ih _ ?_
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc g.matrixᴴ, g.matrix_unitary,
        Matrix.one_mul, h]
  exact key _ _ (by simp)

theorem prep_injective : Function.Injective C.prep := by
  intro s t h
  funext i
  have := congrFun h (Fin.castAdd _ i)
  simpa [prep] using this

open scoped Classical in
/-- **The channel of a circuit**, with one Kraus operator per basis state `e` of the traced wires:
`⟨o| K_e |s⟩ = ⟨o, e| U |s, 0…0⟩`. Every circuit gives a real channel: the relation
`∑ K_e† K_e = 1` is proved here from the unitarity of the gates. -/
noncomputable def channel : QChannel (Fin inW → Fin d) (Fin outW → Fin d) where
  ι := C.Traced → Fin d
  K e := Matrix.of fun o s => C.unitary (C.split.symm (o, e)) (C.prep s)
  complete := by
    ext s t
    have h := congrFun (congrFun C.unitary_unitary (C.prep s)) (C.prep t)
    rw [mul_apply] at h
    rw [← C.split.symm.sum_comp, Fintype.sum_prod_type] at h
    simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, of_apply]
    rw [Finset.sum_comm]
    rw [one_apply] at h ⊢
    simp only [conjTranspose_apply] at h
    rw [h]
    by_cases hst : s = t
    · simp [hst]
    · rw [if_neg hst, if_neg (fun h' => hst (C.prep_injective h'))]

/-- **The output state** `σ` of a circuit run on the all-zero state (Definition 5.5, p.21): the
channel applied to `|0…0⟩⟨0…0|`, the wires not kept being traced out. -/
noncomputable def outputState : Matrix (Fin outW → Fin d) (Fin outW → Fin d) ℂ :=
  let z : Fin inW → Fin d := fun _ => ⟨0, C.d_pos⟩
  C.channel.apply (Matrix.single z z 1)

end Circuit

end FRouting


