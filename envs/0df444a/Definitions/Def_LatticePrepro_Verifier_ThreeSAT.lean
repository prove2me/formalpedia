-- Prove2me | Definitions.Def_LatticePrepro_Verifier_ThreeSAT
-- name    : LatticePrepro_Verifier_ThreeSAT
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:22:59.221559+00:00
-- url     : https://prove2.me/theorems/d40791dc-4b2b-4e5b-bf52-404f338d2f26
-- title:
--   3SAT instances and the 3SAT verifier circuit (the verifier $V_n$ of Theorem 5.1)
-- statement:
--   Fix a number $v$ of variables.
--
--   - **Clauses and instances** (`Clause`, `Instance`): a literal is a pair $(i, s)$ of a variable $i \in \{0, \dots, v-1\}$ and a sign $s \in \{0,1\}$, and a clause is an ordered triple of literals. An instance $x$ is one bit per possible clause, saying which clauses are present. There are $\mathrm{len}(v) = (2v)^3$ possible clauses (`len`, `len_eq`).
--   - **Satisfaction** (`Clause.Satisfied`, `Satisfiable`): an assignment $a \in \{0,1\}^v$ satisfies a clause if $a_i = s$ for one of its literals $(i, s)$, and $x$ is satisfiable if some assignment satisfies every clause present in $x$.
--   - **Encoding** (`clauseEquiv`, `encode`): a fixed enumeration of the clauses by $\{0, \dots, \mathrm{len}(v) - 1\}$, and $\mathrm{encode}(x) \in \{0,1\}^{\mathrm{len}(v)}$ lists the clause bits in this order.
--   - **Leaves** (`numLeaves`, `inputLeaf`, `varLeaf`, `dummyLeaf`): $\mathrm{len}(v) + v + 1$ leaves, namely one input leaf per clause, one leaf per variable, and a dummy leaf used to produce constants.
--   - **Verifier expression** (`litExpr`, `clauseExpr`, `formula`): the literal $(i,s)$ is a gate computing $[\,z = s\,]$ on the leaf $z$ of variable $i$; clause $c$ gives $\text{input}_c \to (\ell_0 \vee (\ell_1 \vee \ell_2))$ for its literals $\ell_0, \ell_1, \ell_2$; and the formula is the conjunction of all clause expressions, in the enumeration order, closed by the constant $1$ computed from the dummy leaf.
--   - **Circuit** (`circuit v`): the Boolean circuit of the formula with $\mathrm{len}(v)$ input wires and $v + 1$ witness wires (an assignment to the variables plus the dummy wire); it has $7\,\mathrm{len}(v) + 1$ gates.
--
--   This is the concrete verifier for 3SAT with which Theorem 5.1 is instantiated; encoding a formula by one bit per possible clause follows the proof of Theorem 5.4. `ThreeSAT.mem_language_iff` shows that the circuit accepts exactly the encodings of satisfiable instances.
--
--   **Formalization Note**: Clauses may repeat variables or literals, since all $(2v)^3$ ordered triples are allowed. The bundle includes $\mathrm{len}(v) = (2v)^3$, the gate counts $1$, $6$ and $7\,\mathrm{len}(v) + 1$ of a literal, a clause and the formula, positivity of the latter, and the numbers of input and witness wires of the circuit.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), the verifier $V_n$ for 3SAT in the proof of Theorem 5.1 (\label{thm:approximation-hardness}), with the instance encoding of the proof of Theorem 5.4 (\label{thm:explicit-endpoint}); Lean: LatticePrepro/Verifier/ThreeSAT.lean, LatticePrepro.ThreeSAT.Satisfiable, LatticePrepro.ThreeSAT.encode, LatticePrepro.ThreeSAT.formula, LatticePrepro.ThreeSAT.circuit

import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr

/-!
# A verifier circuit family for 3SAT (Theorem 5.1: "we take `V = V_n`, a verifier for 3SAT")

Instances of 3SAT on `v` variables are encoded as strings of a common length polynomial in `v`,
listing which of the `(2v)^3` possible clauses are present (as in the proof of Theorem 5.4 of
the paper): a clause is a triple of literals, a literal is a variable together with a sign, and
an instance is one bit per possible clause.

`ThreeSAT.circuit v` is a Boolean circuit (Definition 3.13) with `len v = (2v)^3` input wires and
`v + 1` witness wires (an assignment to the variables, plus one dummy wire used to produce
constants) that checks that every present clause contains a literal satisfied by the
assignment. It accepts exactly the encodings of satisfiable instances
(`ThreeSAT.mem_language_iff`) and has `S = 8 · len v + v + 2 ≤ 9 · len v + 2` wires
(`ThreeSAT.S_circuit_le`), so that `S + 1 ≤ (len v)^3` for `v ≥ 1` (`ThreeSAT.S_succ_le_len_pow`).
-/

namespace LatticePrepro

namespace ThreeSAT

/-- A clause: three literals, each a variable together with a sign. -/
abbrev Clause (v : ℕ) : Type := Fin 3 → Fin v × Bool

/-- An instance on `v` variables: the set of its clauses, one bit per possible clause. -/
abbrev Instance (v : ℕ) : Type := Clause v → Bool

variable {v : ℕ}

/-- A clause is satisfied by an assignment if one of its literals is. -/
def Clause.Satisfied (c : Clause v) (a : Fin v → Bool) : Prop := ∃ j, a (c j).1 = (c j).2

/-- An instance is satisfiable if some assignment satisfies all its clauses. -/
def Satisfiable (x : Instance v) : Prop := ∃ a : Fin v → Bool, ∀ c, x c = true → c.Satisfied a

/-- The instance length: the number `(2v)^3` of possible clauses. -/
def len (v : ℕ) : ℕ := Fintype.card (Clause v)

lemma len_eq (v : ℕ) : len v = (2 * v) ^ 3 := by
  simp only [len, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-- An enumeration of the clauses. -/
def clauseEquiv (v : ℕ) : Clause v ≃ Fin (len v) :=
  ((Equiv.refl (Fin 3)).arrowCongr
    (((Equiv.refl (Fin v)).prodCongr finTwoEquiv.symm).trans finProdFinEquiv)).trans
    (finFunctionFinEquiv.trans (finCongr (by rw [len_eq]; ring)))

/-- The encoding of an instance as a bit string of length `len v`. -/
def encode (x : Instance v) : Fin (len v) → Bool := fun k => x ((clauseEquiv v).symm k)

/-! ### The verifier expression -/

/-- The number of leaves of the verifier expression: the input bits, then the witness bits. -/
abbrev numLeaves (v : ℕ) : ℕ := len v + (v + 1)

/-- The leaf carrying the input bit of clause `c`. -/
def inputLeaf (c : Clause v) : Fin (numLeaves v) := Fin.castAdd (v + 1) (clauseEquiv v c)

/-- The leaf carrying the witness bit of variable `i`. -/
def varLeaf (i : Fin v) : Fin (numLeaves v) := Fin.natAdd (len v) (Fin.castSucc i)

/-- The dummy leaf (the last witness wire), used to produce constants. -/
def dummyLeaf (v : ℕ) : Fin (numLeaves v) := Fin.natAdd (len v) (Fin.last v)

/-- The literal `l = (i, s)` is satisfied: `a i == s`. -/
def litExpr (l : Fin v × Bool) : BExpr (numLeaves v) :=
  BExpr.eqConst l.2 (BExpr.leaf (varLeaf l.1))

/-- Clause `c`, if present, is satisfied. -/
def clauseExpr (c : Clause v) : BExpr (numLeaves v) :=
  BExpr.imp (BExpr.leaf (inputLeaf c))
    (BExpr.or (litExpr (c 0)) (BExpr.or (litExpr (c 1)) (litExpr (c 2))))

/-- The verifier expression: every present clause is satisfied. -/
def formula (v : ℕ) : BExpr (numLeaves v) :=
  BExpr.bigAnd (dummyLeaf v)
    ((List.finRange (len v)).map fun k => clauseExpr ((clauseEquiv v).symm k))

@[simp] lemma size_litExpr (l : Fin v × Bool) : (litExpr l).size = 1 := rfl

@[simp] lemma size_clauseExpr (c : Clause v) : (clauseExpr c).size = 6 := rfl

lemma size_formula (v : ℕ) : (formula v).size = 7 * len v + 1 := by
  rw [formula, BExpr.size_bigAnd, List.map_map, List.length_map, List.length_finRange]
  have : (List.finRange (len v)).map (BExpr.size ∘ fun k => clauseExpr ((clauseEquiv v).symm k)) =
      (List.finRange (len v)).map fun _ => 6 := List.map_congr_left fun _ _ => rfl
  rw [this, List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul]
  ring

lemma size_formula_pos (v : ℕ) : 0 < (formula v).size := by
  rw [size_formula]; omega

/-! ### The circuit -/

/-- The verifier circuit for 3SAT on `v` variables: `len v` input wires, `v + 1` witness wires
(an assignment and a dummy wire), and the gates of the verifier expression. -/
abbrev circuit (v : ℕ) : BoolCircuit :=
  BExpr.toCircuit (len v) (v + 1) (formula v) (size_formula_pos v)

@[simp] lemma circuit_n (v : ℕ) : (circuit v).n = len v := rfl

@[simp] lemma circuit_w (v : ℕ) : (circuit v).w = v + 1 := rfl

end ThreeSAT

end LatticePrepro


