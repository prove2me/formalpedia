-- Prove2me | Definitions.Def_NCFactorClosure607_Circuits_Supplement_Encoding
-- name    : NCFactorClosure607_Circuits_Supplement_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:08:16.879465+00:00
-- url     : https://prove2.me/theorems/1207fd51-b279-4944-8246-8e8fc29db826
-- title:
--   Explicit finite fields $\mathbb F_p[t]/(\varphi)$, binary encodings of circuits, and complete ordered factorizations
-- statement:
--   **Explicit finite field.** $\mathbb F_q=\mathbb F_p[t]/(\varphi(t))$ for a prime $p$ and a monic irreducible $\varphi\in\mathbb F_p[t]$, $q=p^{\deg\varphi}$. An element is written as the coefficients (integers in $[0,p)$, in binary) of its representative of degree $<\deg\varphi$, so it takes $O(\log q)$ bits.
--
--   **Bit strings.** A string is made self-delimiting by doubling each bit and appending $01$; a tuple of strings is the concatenation of these codes. Natural numbers are in binary, the degree bound $D$ in unary. A gate is a two-bit tag followed by its constant, its variable index, or its two operand positions; a circuit is the tuple of its gates. The input of the factorization algorithms is the tuple $(p,\varphi,m,C,1^D)$; the output is the tuple $(\lambda,C_1,\dots,C_k)$.
--
--   **Factorizations.** A polynomial is *constant* when it equals $a\cdot1$ for some $a\in F$. A nonconstant polynomial is *irreducible* when it is not a product of two nonconstant polynomials. A *complete ordered factorization* of $f\neq0$ is
--   $$f=\lambda f_1\cdots f_k,\qquad \lambda\in F\setminus\{0\},$$
--   with every $f_i$ nonconstant and irreducible; the list is empty exactly when $f$ is a scalar. A bit string is a **correct factorization output** for $f$ when it is the encoding of $\lambda$ and well-formed circuits $C_1,\dots,C_k$ over $\mathbb F_q$ in the input variables whose polynomials form a complete ordered factorization of $f$.
--
--   These encodings fix the input and output conventions of Theorems 7.2, 8.1 and 8.2.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.5, §2 (factors, irreducibility, complete factorizations); p.6, §2.1 last paragraph; p.17, §7 opening; p.18, §8 opening; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Circuit
import Definitions.Def_NCFactorClosure607_Circuits_Polynomials

/-!
# Explicit finite fields, binary encodings, and complete ordered factorizations

Arvind–Joglekar, *Factor Closure in Noncommutative Algebraic Complexity*,
STOC 2027 submission #607, §2, p.5 (factors, irreducibility, complete factorizations), §2.1,
last paragraph, p.6 (explicitly represented finite fields), §7 opening, p.17, and §8 opening,
p.18.

**Explicit finite field.** `F_q = F_p[t]/(φ(t))` for a prime `p` and a monic irreducible
`φ ∈ F_p[t]` (Lean: `AdjoinRoot φ` with `φ : (ZMod p)[X]`), `q = p^{deg φ}`. A field element is
written as the coefficient vector of its unique representative of degree `< deg φ`, each
coefficient in binary, so it takes `O(log q)` bits.

**Bit strings.** A string `x` is made self-delimiting by doubling each bit and appending `01`
(`code`); a tuple of strings is the concatenation of their codes (`tuple`). Natural numbers are
written in binary (Mathlib's `Nat.bits`, least significant bit first); a degree bound `D` is
written in unary (`D` ones).

**Circuits** over `F_q` in the variables `x_0, …, x_{m-1}` (Lean: `Fin m`) are written as the
tuple of their gates; a gate is a two-bit tag followed by its field constant, its variable index,
or its two operand positions.

**Factorizations** (p.5). `P` is *constant* (a scalar) when `P = a · 1` for some `a ∈ F`; a
nonconstant `P` is *irreducible* when it is not a product of two nonconstant polynomials. A
*complete ordered factorization* of `f ≠ 0` is `f = λ f_1 ⋯ f_k` with `λ ∈ F` nonzero and every
`f_i` nonconstant and irreducible; the list is empty exactly for a scalar `f`.
-/

namespace NCFactorClosure607.Circuits.Supplement

open NCFactorClosure607.Circuits Polynomial

/-! ## Bit strings -/

/-- The self-delimiting code of a bit string: every bit doubled, then `01`. -/
def code (x : List Bool) : List Bool := x.flatMap (fun b => [b, b]) ++ [false, true]

/-- The encoding of a tuple of bit strings: the concatenation of their codes. -/
def tuple (xs : List (List Bool)) : List Bool := xs.flatMap code

/-- A natural number in binary (least significant bit first; `0` is the empty string). -/
def bin (n : ℕ) : List Bool := n.bits

/-- A natural number in unary. -/
def unary (n : ℕ) : List Bool := List.replicate n true

/-! ## Explicit finite fields -/

section ExplicitField

variable {p : ℕ} {φ : (ZMod p)[X]}

/-- The encoding of an element `a ∈ F_p[t]/(φ)`: the binary codes of the `deg φ` coefficients
(as integers in `[0, p)`) of its representative of degree `< deg φ`. -/
noncomputable def encElt (hφ : φ.Monic) (a : AdjoinRoot φ) : List Bool :=
  tuple ((List.range φ.natDegree).map fun i => bin ((AdjoinRoot.modByMonicHom hφ a).coeff i).val)

/-- The encoding of the defining polynomial `φ`: its `deg φ + 1` coefficients in binary. -/
noncomputable def encModulus (φ : (ZMod p)[X]) : List Bool :=
  tuple ((List.range (φ.natDegree + 1)).map fun i => bin (φ.coeff i).val)

/-- `q = p ^ deg φ`, the number of elements of `F_p[t]/(φ)`. -/
noncomputable def fieldCard (p : ℕ) (φ : (ZMod p)[X]) : ℕ := p ^ φ.natDegree

variable {m : ℕ}

/-- The encoding of a gate of a circuit over `F_p[t]/(φ)` in the variables `Fin m`. -/
noncomputable def encGate (hφ : φ.Monic) : Gate (AdjoinRoot φ) (Fin m) → List Bool
  | .const a => tuple [[false, false], encElt hφ a]
  | .var x => tuple [[false, true], bin x.val]
  | .add i j => tuple [[true, false], bin i, bin j]
  | .mul i j => tuple [[true, true], bin i, bin j]

/-- The encoding of a circuit: the tuple of its gates, in order. -/
noncomputable def encCircuit (hφ : φ.Monic) (C : Circuit (AdjoinRoot φ) (Fin m)) : List Bool :=
  tuple (C.gates.map (encGate hφ))

/-- The input of the factorization algorithms (§8 opening, p.18): the field (`p` in binary and
the coefficients of `φ`), the number `m` of variables, the circuit, and the degree bound `D` in
unary. -/
noncomputable def encFactorInput (hφ : φ.Monic) (C : Circuit (AdjoinRoot φ) (Fin m)) (D : ℕ) :
    List Bool :=
  tuple [bin p, encModulus φ, bin m, encCircuit hφ C, unary D]

/-- The output of the factorization algorithms: a scalar followed by a list of circuits. -/
noncomputable def encFactorOutput (hφ : φ.Monic) (lam : AdjoinRoot φ)
    (Cs : List (Circuit (AdjoinRoot φ) (Fin m))) : List Bool :=
  tuple (encElt hφ lam :: Cs.map (encCircuit hφ))

end ExplicitField

/-! ## Complete ordered factorizations -/

section Factorization

variable {F : Type*} [Field F] {X : Type*}

/-- `P` is constant (a scalar): `P = a · 1` for some `a ∈ F`. -/
def IsScalar (P : FreeAlgebra F X) : Prop := ∃ a : F, P = algebraMap F (FreeAlgebra F X) a

/-- `P` is irreducible (p.5): nonconstant, and not a product of two nonconstant polynomials. -/
def IsNCIrreducible (P : FreeAlgebra F X) : Prop :=
  ¬ IsScalar P ∧ ∀ g h : FreeAlgebra F X, P = g * h → IsScalar g ∨ IsScalar h

/-- `f = λ f_1 ⋯ f_k` is a complete ordered factorization (p.5): `λ ≠ 0`, every `f_i` is
nonconstant and irreducible, the ordered product times `λ` is `f`, and the list is empty exactly
when `f` is a scalar. -/
def IsCompleteFactorization (f : FreeAlgebra F X) (lam : F) (fs : List (FreeAlgebra F X)) :
    Prop :=
  lam ≠ 0 ∧ (∀ P ∈ fs, IsNCIrreducible P) ∧
    f = algebraMap F (FreeAlgebra F X) lam * fs.prod ∧ (fs = [] ↔ IsScalar f)

end Factorization

/-- The bit string `y` is the encoding of a correct output for `f` (§8 opening, p.18): a scalar
`λ` and a list of well-formed circuits over the input field, in the input variables, which
together form a complete ordered factorization of `f`. -/
def IsFactorizationOutput {p : ℕ} [Fact p.Prime] {φ : (ZMod p)[X]} [Fact (Irreducible φ)] (hφ : φ.Monic)
    {m : ℕ} (f : FreeAlgebra (AdjoinRoot φ) (Fin m)) (y : List Bool) : Prop :=
  ∃ (lam : AdjoinRoot φ) (Cs : List (Circuit (AdjoinRoot φ) (Fin m))),
    y = encFactorOutput hφ lam Cs ∧ (∀ C ∈ Cs, C.WellFormed) ∧
      IsCompleteFactorization f lam (Cs.map Circuit.eval)

end NCFactorClosure607.Circuits.Supplement


