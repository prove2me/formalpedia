-- Prove2me | Definitions.Def_ShiShallow_Matrix
-- name    : ShiShallow_Matrix
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-11T04:31:24.530827+00:00
-- url     : https://prove2.me/theorems/66155222-d5c8-43f7-a49a-e2cddbefdfb5
-- title:
--   Operator layer for shallow quantum circuits: gate, layer and circuit matrices (definitions)
-- statement:
--   **Operator (matrix) layer for shallow quantum circuits.** Definitions only.
--
--   This bundle EXTENDS the published `ShiShallow_Core` definition bundle rather than duplicating it: it imports that module and reuses `Bits`, `Instr`, `Layered` and the one-qubit matrices, so the two can be imported together and a theorem may mix the state-vector and matrix layers.
--
--   For each instruction, layer and layered circuit it gives the induced operator on the $2^n$-dimensional space indexed by basis strings:
--
--   $$\\mathrm{layerMatrix}(g::t)=\\mathrm{layerMatrix}(t)\\cdot\\mathrm{gateMatrix}(g),\\qquad \\mathrm{circMatrix}(\\ell::t)=\\mathrm{circMatrix}(t)\\cdot\\mathrm{layerMatrix}(\\ell),$$
--
--   the products being reversed relative to application order because gates apply left to right. It also provides a locality predicate $\\mathrm{IsLocal}\\,S\\,A$ expressing $A=A_S\\otimes I$ without tensor products, the reconstruction map $\\mathrm{graft}$, the input padding $\\mathrm{padIn}$, and the projector $\\mathrm{projOut}$ onto a chosen output wire reading $1$.
--
--   **Definitions only.** No theorem is exported, so that each provable fact remains independently citable. In particular nothing here proves that $\\mathrm{gateMatrix}$, $\\mathrm{layerMatrix}$ or $\\mathrm{circMatrix}$ is unitary, that they agree with the state-vector semantics of the core bundle, that $\\mathrm{IsLocal}$ is closed under products, or that $\\mathrm{projOut}$ is idempotent or local. $\\mathrm{IsLocal}$ is defined but never applied to any matrix within this bundle.
--
--   **Caveat, documented at the declaration.** $\\mathrm{cnotMatrix}\\,i\\,j$ takes no hypothesis $i\\neq j$ and at $i=j$ is rank-deficient — neither CNOT nor unitary. $\\mathrm{gateMatrix}$ holds such a hypothesis inside the `Instr.cnot` constructor but discards it, so nothing in the types enforces distinctness.

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Operator (matrix) layer for shallow quantum circuits -- DEFINITIONS ONLY.

This bundle EXTENDS the published `ShiShallow_Core` definition bundle rather than
duplicating it: it imports that module and reuses exactly `Bits`, `Instr` (with its five constructors),
`Layered`, and the one-qubit matrices `hMat`, `sMat`, `tMat`, `xMat`. It does NOT use that
bundle's `QState` or `apply1`: `apply1Matrix` below is built directly from `Matrix.of` and
takes an arbitrary `U`, so nothing here connects the matrix layer to the state-vector
semantics. No name from that bundle is redefined here, so the two may be imported together
and a theorem may mix the two layers.

Every public theorem has been REMOVED so that none is buried inside a definition entry (a
lemma published inside a definition bundle can never afterwards be submitted as a theorem --
its name is already declared in the environment). Those lemmas are submitted separately.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

/-!
# Operator layer: matrices of gates, layers and circuits

For each instruction, layer and layered circuit this bundle gives the induced operator on
the `2 ^ n`-dimensional state space, indexed by basis strings, together with a locality
predicate `IsLocal S A` expressing `A = A_S ⊗ I` without tensor products, and the projector
`projOut` onto a chosen output wire being `1`.

DEFINITIONS ONLY -- no theorem is exported. In particular nothing here proves that
`gateMatrix`, `layerMatrix` or `circMatrix` is unitary, that they agree with the
state-vector semantics `Instr.apply`/`runLayer`/`runLayered` of `ShiShallow_Core`, that
`IsLocal` is closed under products, that `projOut` is idempotent or `{out}`-local, or that
any matrix here is `IsLocal` for any wire set at all -- `IsLocal` is defined but never
applied within this bundle.

CAVEAT, inherited and documented at the declaration: `cnotMatrix i j` takes NO hypothesis
`i ≠ j`, and at `i = j` it is rank-deficient -- not CNOT and not unitary. `gateMatrix` holds
such a hypothesis inside the `Instr.cnot` constructor but discards it when calling
`cnotMatrix`, so nothing in the types enforces distinctness.

Matrix products are REVERSED relative to application order: gates in a layer apply left to
right, so `layerMatrix (g :: t) = layerMatrix t * gateMatrix g`, and likewise for circuits.
-/

namespace ShiShallow

/-- An operator on `n` qubits. -/
abbrev Op (n : ℕ) := Matrix (Bits n) (Bits n) ℂ

/-- Overwrite `v` on `S` with the values carried by `w`. -/
-- NOTE: `graft` is not consumed by any other definition in this bundle. It reconstructs a
-- full basis string from a restriction, which is precisely the operation `IsLocal`'s
-- conjunction form was chosen to avoid needing; it is retained for downstream theorems.
def graft {n : ℕ} (S : Finset (Fin n)) (v : Bits n)
    (w : {k : Fin n // k ∈ S} → Bool) : Bits n :=
  fun k => if h : k ∈ S then w ⟨k, h⟩ else v k

/-- `A` acts as the identity outside `S`: entries vanish unless the two basis strings agree
off `S`, and otherwise depend only on the restrictions to `S`. This is the tensor-product
condition `A = A_S ⊗ I`, written without tensor products.

Stated as a conjunction rather than as `∃ B, ...` because both halves get used directly by
the conjugation lemmas of the wider development, where reconstructing a full basis string from
a restriction would otherwise be needed inside a double sum. NOTE: those lemmas are NOT in
this bundle -- it exports no theorem -- so within this file the choice of formulation has no
justification a reader can check here. -/
def IsLocal {n : ℕ} (S : Finset (Fin n)) (A : Op n) : Prop :=
  (∀ y z : Bits n, (¬ ∀ k, k ∉ S → y k = z k) → A y z = 0) ∧
  (∀ y z y' z' : Bits n, (∀ k ∈ S, y k = y' k) → (∀ k ∈ S, z k = z' k) →
      (∀ k, k ∉ S → y k = z k) → (∀ k, k ∉ S → y' k = z' k) → A y z = A y' z')

/-- Matrix of a one-qubit gate on wire `i`, written so that `{i}`-locality is manifest. -/
def apply1Matrix {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) : Op n :=
  Matrix.of fun y z =>
    if (∀ k, k ∉ ({i} : Finset (Fin n)) → y k = z k) then U (y i) (z i) else 0

/-- Matrix of CNOT (control `i`, target `j`), written so that `{i,j}`-locality is manifest.

CAVEAT: unlike `cnotState`, this definition takes NO `i ≠ j` hypothesis, and at `i = j` it is
NOT the CNOT matrix: the predicate collapses to `z i = y i ∧ z i = false`, whose only nonzero
entries have `y i = z i = false`, giving a rank-deficient and non-unitary matrix. Callers must
supply `i ≠ j` themselves. `gateMatrix` does hold such a hypothesis inside the `Instr.cnot`
constructor but discards it when calling this definition, so nothing in the types enforces
it. -/
def cnotMatrix {n : ℕ} (i j : Fin n) : Op n :=
  Matrix.of fun y z =>
    if (∀ k, k ∉ ({i, j} : Finset (Fin n)) → y k = z k) ∧ z i = y i ∧ z j = xor (y j) (y i)
    then 1 else 0

/-- The matrix of an instruction. -/
noncomputable def gateMatrix {n : ℕ} : Instr n → Op n
  | .h i => apply1Matrix hMat i
  | .s i => apply1Matrix sMat i
  | .t i => apply1Matrix tMat i
  | .x i => apply1Matrix xMat i
  | .cnot i j _ => cnotMatrix i j

/-- The matrix of a layer. Gates are applied left to right, so the matrix product is reversed. -/
noncomputable def layerMatrix {n : ℕ} : List (Instr n) → Op n
  | [] => 1
  | g :: t => layerMatrix t * gateMatrix g

/-- The matrix of a layered circuit. -/
noncomputable def circMatrix {n : ℕ} : Layered n → Op n
  | [] => 1
  | l :: t => circMatrix t * layerMatrix l

/-- The computational-basis input string: `x` on the input wires, zeros on the ancillas.

Written with `Fin.append`. The imported core bundle separately defines `inputState`, which
encodes the same data in a different way; NO lemma anywhere relates the two, and nothing in
this bundle consumes `padIn`. -/
def padIn {n m : ℕ} (x : Bits n) : Bits (n + m) := Fin.append x (fun _ => false)

/-- The measurement observable: the projector onto `out = 1`, as a diagonal 0/1 matrix.
No property of it is proved here -- in particular neither idempotence nor `IsLocal {out}`,
though both are true. `IsLocal` is never applied to any matrix in this bundle. -/
def projOut {n : ℕ} (out : Fin n) : Op n :=
  Matrix.of fun y z => if y = z ∧ y out = true then 1 else 0

end ShiShallow


