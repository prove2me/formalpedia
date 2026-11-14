-- Prove2me | Definitions.Def_LatticePrepro_Verifier_Gates
-- name    : LatticePrepro_Verifier_Gates
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:19:56.73693+00:00
-- url     : https://prove2.me/theorems/ce11b915-66ba-4a4d-9fd9-7811bfd52afb
-- title:
--   Gate verifiers and quadratic gate equations (Definition 3.14, Claim 3.15)
-- statement:
--   - **Gate verifier** (`GateVerifier`): an instance length $n$, a number $S \ge n + 1$ of wires numbered $0, \dots, S-1$, and $G$ gates; gate $b$ is a tuple $(o_b, l_b, l'_b, f_b)$ of an output wire, two input wires and a Boolean function $f_b\colon \{0,1\}^2 \to \{0,1\}$ (`out`, `in1`, `in2`, `fn`). Wires $0, \dots, n-1$ are the input wires (`inputWire`) and wire $n$ is the output wire (`outputWire`).
--   - A wire assignment $z \in \{0,1\}^S$ is **valid** (`IsValid`) if $z_{o_b} = f_b(z_{l_b}, z_{l'_b})$ for every gate $b$, and has **prefix** $(x, 1)$ (`HasPrefix`) if $z_i = x_i$ for $i < n$ and $z_n = 1$. The **language** is $L(W) = \{x \in \{0,1\}^n : \text{some valid } z \text{ has prefix } (x, 1)\}$.
--   - **Multilinear interpolation** (`c00`, `c10`, `c01`, `c11`): for $f\colon \{0,1\}^2 \to \{0,1\}$, the integers $c_{00} = f(0,0)$, $c_{10} = f(1,0) - f(0,0)$, $c_{01} = f(0,1) - f(0,0)$ and $c_{11} = f(1,1) - f(1,0) - f(0,1) + f(0,0)$, so that $f(u, v) = c_{00} + c_{10}u + c_{01}v + c_{11}uv$ on $\{0,1\}^2$.
--   - `deltaTensor i₀ j₀ c`: the coefficient tensor of the single monomial $c \cdot z_{i_0} z_{j_0}$.
--   - **Quadratic verifier of a gate verifier** (`toQuadratic p`): the quadratic verifier over $\mathbb{F}_p$ with the same $n$, $S$, $G$, whose coordinates are $z_0$ (the constant coordinate) and $z_1, \dots, z_S$, wire $i$ becoming coordinate $i + 1$. Gate $b$ becomes the homogeneous quadratic equation
--   $$z_0\, z_{o_b+1} - c_{00}\, z_0^2 - c_{10}\, z_0\, z_{l_b+1} - c_{01}\, z_0\, z_{l'_b+1} - c_{11}\, z_{l_b+1}\, z_{l'_b+1} = 0,$$
--   with the coefficients of $f_b$ reduced modulo $p$.
--
--   This implements Claim 3.15: interpolate each gate's truth table over $\mathbb{F}_p$ and homogenize with the constant coordinate $z_0 = 1$. `GateVerifier.language_toQuadratic` shows that the quadratic verifier has the same language; gate verifiers arise from Boolean circuits by ordering the wires as in Definition 3.14.
--
--   **Formalization Note**: A gate verifier is a general system of Boolean gate constraints; acyclicity is not required (`BoolCircuit.toGateVerifier` produces one from a circuit). The bundle includes simp lemmas stating that `toQuadratic` preserves $n$, $S$ and $G$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Definition 3.14 (\label{def:computation-assignment}) and Claim 3.15 (\label{clm:verifier-system}); Lean: LatticePrepro/Verifier/Gates.lean, LatticePrepro.GateVerifier, LatticePrepro.GateVerifier.Language, LatticePrepro.GateVerifier.toQuadratic

import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic

/-!
# Gate verifiers and quadratic gate equations (Definitions 3.13–3.14, Claim 3.15)

A *gate verifier* is a system of Boolean constraints `z_o = f(z_l, z_{l'})` with fan-in two on
wires `Fin S`: wires `0, …, n-1` carry the instance, wire `n` is the output wire, and the remaining
wires carry the witness and the gate outputs. An assignment is *valid* if every gate constraint
holds, and the language consists of the instances `x` with a valid assignment with prefix
`(x, true)`.

Following Claim 3.15, each gate function `f : Bool → Bool → Bool` is interpolated by the
multilinear polynomial `a + b u + c v + d u v` with integer coefficients, and the gate constraint
becomes the homogeneous quadratic equation
`z_0 z_o - a z_0 z_0 - b z_0 z_l - c z_0 z_{l'} - d z_l z_{l'} = 0`
over `𝔽_p`, where `z_0 = 1` is the constant coordinate. The resulting `QuadraticVerifier` has the
same language (`GateVerifier.language_toQuadratic`).
-/

namespace LatticePrepro

/-! ### Quadratic forms given by coefficient tensors -/

section QuadForm

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The coefficient tensor of the single monomial `c · z_{i₀} z_{j₀}`. -/
def deltaTensor [DecidableEq (Fin m)] (i₀ j₀ : Fin m) (c : R) : Fin m → Fin m → R :=
  fun i j => if i = i₀ ∧ j = j₀ then c else 0

end QuadForm

/-- A verifier given by Boolean gates of fan-in two on wires `Fin S` (Definition 3.13):
wires `0, …, n - 1` are the inputs, wire `n` is the output, and each gate
`(o, l, l', f)` imposes `z o = f (z l) (z l')`. -/
structure GateVerifier where
  /-- Instance length. -/
  n : ℕ
  /-- Number of wires. -/
  S : ℕ
  /-- The input wires and the output wire fit. -/
  n_succ_le : n + 1 ≤ S
  /-- Number of gates. -/
  G : ℕ
  /-- The gates `(output wire, input wire 1, input wire 2, gate function)`. -/
  gate : Fin G → Fin S × Fin S × Fin S × (Bool → Bool → Bool)

namespace GateVerifier

variable (W : GateVerifier)

/-- The output wire of a gate. -/
def out (b : Fin W.G) : Fin W.S := (W.gate b).1
/-- The first input wire of a gate. -/
def in1 (b : Fin W.G) : Fin W.S := (W.gate b).2.1
/-- The second input wire of a gate. -/
def in2 (b : Fin W.G) : Fin W.S := (W.gate b).2.2.1
/-- The Boolean function of a gate. -/
def fn (b : Fin W.G) : Bool → Bool → Bool := (W.gate b).2.2.2

/-- An assignment to the wires is valid if every gate is evaluated correctly. -/
def IsValid (z : Fin W.S → Bool) : Prop :=
  ∀ b, z (W.out b) = W.fn b (z (W.in1 b)) (z (W.in2 b))

/-- The `i`-th input wire. -/
def inputWire (i : Fin W.n) : Fin W.S := ⟨i.val, by have := W.n_succ_le; omega⟩

/-- The output wire `n`. -/
def outputWire : Fin W.S := ⟨W.n, by have := W.n_succ_le; omega⟩

/-- The assignment has prefix `(x, true)`. -/
def HasPrefix (x : Fin W.n → Bool) (z : Fin W.S → Bool) : Prop :=
  (∀ i, z (W.inputWire i) = x i) ∧ z W.outputWire = true

/-- The language of the gate verifier (Definition 3.13). -/
def Language : Set (Fin W.n → Bool) := {x | ∃ z, W.IsValid z ∧ W.HasPrefix x z}

/-! ### Multilinear interpolation of a gate function -/

/-- Constant coefficient `a = f 0 0`. -/
def c00 (f : Bool → Bool → Bool) : ℤ := (f false false).toNat
/-- Coefficient of `u`: `b = f 1 0 - f 0 0`. -/
def c10 (f : Bool → Bool → Bool) : ℤ := (f true false).toNat - (f false false).toNat
/-- Coefficient of `v`: `c = f 0 1 - f 0 0`. -/
def c01 (f : Bool → Bool → Bool) : ℤ := (f false true).toNat - (f false false).toNat
/-- Coefficient of `u v`: `d = f 1 1 - f 1 0 - f 0 1 + f 0 0`. -/
def c11 (f : Bool → Bool → Bool) : ℤ :=
  (f true true).toNat - (f true false).toNat - (f false true).toNat + (f false false).toNat

/-! ### The quadratic verifier of a gate verifier -/

/-- The quadratic verifier of Claim 3.15: the gate `(o, l, l', f)` becomes the equation
`z_0 z_o - a z_0 z_0 - b z_0 z_l - c z_0 z_{l'} - d z_l z_{l'} = 0`. -/
abbrev toQuadratic (p : ℕ) : QuadraticVerifier p where
  n := W.n
  S := W.S
  n_succ_le := W.n_succ_le
  G := W.G
  coeff := fun b =>
    deltaTensor 0 (W.out b).succ 1 - deltaTensor 0 0 ((c00 (W.fn b) : ℤ) : ZMod p) -
      deltaTensor 0 (W.in1 b).succ ((c10 (W.fn b) : ℤ) : ZMod p) -
      deltaTensor 0 (W.in2 b).succ ((c01 (W.fn b) : ℤ) : ZMod p) -
      deltaTensor (W.in1 b).succ (W.in2 b).succ ((c11 (W.fn b) : ℤ) : ZMod p)

variable (p : ℕ)

@[simp] lemma toQuadratic_n : (W.toQuadratic p).n = W.n := rfl
@[simp] lemma toQuadratic_S : (W.toQuadratic p).S = W.S := rfl
@[simp] lemma toQuadratic_G : (W.toQuadratic p).G = W.G := rfl

variable [Fact p.Prime]

end GateVerifier

end LatticePrepro


