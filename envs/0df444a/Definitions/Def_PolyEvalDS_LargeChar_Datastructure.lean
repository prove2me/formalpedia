-- Prove2me | Definitions.Def_PolyEvalDS_LargeChar_Datastructure
-- name    : PolyEvalDS_LargeChar_Datastructure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:18.887491+00:00
-- url     : https://prove2.me/theorems/b7ecb569-6bcb-40ae-8d39-a923f156982a
-- title:
--   Algebraic polynomial evaluation datastructure (Definition 2.2) for a family of parameters
-- statement:
--   Definition 2.2 for evaluation-table encodings, stated uniformly over a family of parameters.
--
--   An **instance** $I=(p,n,d,B,t,\mathrm{aux})$ gives the characteristic, the number of variables, the degree bound, the input bound $B$ (input points lie in $\{0,\dots,B\}^n$), the grid bound $t$ (cells are indexed by $\{0,\dots,t\}^n$), and an auxiliary number. For a field $F$ with $\mathbb F_p\to F$ and $f\in F[X_1,\dots,X_n]$, the **cell** at $x\in\mathbb N^n$ is
--   $$f(x_1 \bmod p,\dots,x_n\bmod p),$$
--   so the encoding map is $f\mapsto (f(x))_{x\in\{0,\dots,t\}^n}$, of size $s=(t+1)^n$. If $t\ge p$, several indices name the same point.
--
--   **Decoding at $a$.** A list $i_1,\dots,i_l$ of indices and a formula $e$ *decode at $a$* if all indices lie in $\{0,\dots,t\}^n$, the variables of $e$ are below $l$, and for every field $F\supseteq\mathbb F_p$ and every $f$ of total degree at most $d$,
--   $$e\bigl(f(i_1),\dots,f(i_l)\bigr)=f(a).$$
--   The list and $e$ are fixed before $F$ and $f$.
--
--   **Encoding circuits with exponent $c$.** One formula per box point over the coefficients of $f$, of total size at most $s^c$, computing the cell at that point, for every field $F\supseteq\mathbb F_p$ and every $f$ of total degree at most $d$.
--
--   **Family predicate.** Given instances $I_i$ and real bounds $Q_i$ indexed by $i\in\iota$, $\mathrm{DS}(I,Q)$ asserts that there are one multi-stack Turing machine with Boolean input and output alphabets, one polynomial $T$ and one number $c$ such that for all $i$: the encoding circuits with exponent $c$ exist, and for every $a\in\{0,\dots,B\}^n$ there are indices and a formula decoding at $a$, with at most $Q_i$ indices, such that the machine started on the code of $(I_i,a)$ halts with the code of those indices and that formula within $T(\Lambda_i)$ steps, where
--   $$\Lambda_i=n+|p|+d+|B|+|t|+|\mathrm{aux}|+\lceil Q_i\rceil$$
--   and $|\cdot|$ is the bit size. The machine sees $I_i$, not $i$.
--
--   This is the object every datastructure statement of the mission asserts.
--
--   **Formalization Note** The step bound includes $Q$ because the algorithm must print up to $Q$ indices, and $Q$ is not polynomial in the input size (p. 3). `HMBinPacking.OutputsWithin` is the published run notion over Mathlib's `Turing.TM2OutputsInTime`.
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, Definition 2.2, p. 5; §1.1, p. 3; §2.1 footnote 1, p. 5

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_PolyEvalDS_LargeChar_Formula
import Definitions.Def_PolyEvalDS_LargeChar_Encoding

namespace PolyEvalDS.LargeChar

universe u

/-- The data a datastructure's query algorithm receives: the characteristic `p`, the number of
variables `n`, the degree bound `d`, the input bound `B` (input points lie in `{0,…,B}^n`), the
grid bound `t` (cells are indexed by `{0,…,t}^n`), and `aux`, the parameter `r` in Proposition 3.2
and `0` otherwise. -/
structure DSInstance where
  p : ℕ
  n : ℕ
  d : ℕ
  B : ℕ
  t : ℕ
  aux : ℕ

/-- The cell of the encoding of `f` at index `x ∈ ℕ^n`: the value of `f` at `x` reduced to `F_p^n`.
This is the encoding map `f ↦ (f(a))_a`; several indices name the same point when `t ≥ p`. -/
noncomputable def cellValue (p : ℕ) {n : ℕ} {F : Type u} [Field F] [Algebra (ZMod p) F]
    (f : MvPolynomial (Fin n) F) (x : Fin n → ℕ) : F :=
  MvPolynomial.eval (fun i => algebraMap (ZMod p) F ((x i : ℕ) : ZMod p)) f

/-- The word on the machine's input stack: `p, n, d, B, t, aux`, then `a₀,…,a_{n−1}`. -/
def inputWord (I : DSInstance) (a : Fin I.n → ℕ) : List Bool :=
  encNat I.p ++ encNat I.n ++ encNat I.d ++ encNat I.B ++ encNat I.t ++ encNat I.aux ++
    (List.ofFn a).flatMap encNat

/-- The word on the machine's output stack: the list of cell indices, then the formula. -/
def outputWord (I : DSInstance) (idx : List (Fin I.n → ℕ)) (e : AF ℕ) : List Bool :=
  encList encPoint idx ++ encAF e

/-- Decoding correctness at the input point `a`: all indices of `idx` lie in `{0,…,t}^n`, the
variables of `e` name positions of `idx`, and for **every** field `F ⊇ F_p` and every polynomial of
total degree at most `d`, evaluating `e` on the cells of `idx` gives `f(a)`. `idx` and `e` are fixed
before `F` and `f`. -/
def DecodesAt (I : DSInstance) (a : Fin I.n → ℕ) (idx : List (Fin I.n → ℕ)) (e : AF ℕ) : Prop :=
  (∀ x ∈ idx, ∀ j, x j ≤ I.t) ∧ e.VarsBelow idx.length ∧
    ∀ (F : Type u) [Field F] [Algebra (ZMod I.p) F] (f : MvPolynomial (Fin I.n) F),
      f.totalDegree ≤ I.d →
        e.eval (fun j => cellValue I.p f (idx.getD j (fun _ => 0))) = cellValue I.p f a

/-- The monomials of total degree at most `d`: the coefficient variables of the encoding circuit. -/
abbrev BoundedMonomial (I : DSInstance) : Type :=
  {m : Fin I.n →₀ ℕ // m.degree ≤ I.d}

/-- The encoding circuit of Definition 2.2 with exponent `c`: one formula per box point, over the
coefficients of the polynomial, of total size at most `s^c` where `s = (t+1)^n`, computing the cell
at that point, for every field `F ⊇ F_p` and every polynomial of total degree at most `d`. -/
def EncodingCircuits (I : DSInstance) (c : ℕ) : Prop :=
  ∃ ψ : (Fin I.n → Fin (I.t + 1)) → AF (BoundedMonomial I),
    (∑ x, (ψ x).size) ≤ ((I.t + 1) ^ I.n) ^ c ∧
      ∀ (F : Type u) [Field F] [Algebra (ZMod I.p) F] (f : MvPolynomial (Fin I.n) F),
        f.totalDegree ≤ I.d →
          ∀ x, (ψ x).eval (fun m => MvPolynomial.coeff m.1 f) =
            cellValue I.p f (fun i => ((x i : Fin (I.t + 1)) : ℕ))

/-- The parameter a machine's step bound is a polynomial of: `n`, the bit sizes of `p`, `B`, `t`,
`aux`, `d` in unary, and the query bound `Q`. -/
noncomputable def timeParam (I : DSInstance) (Q : ℝ) : ℕ :=
  I.n + Nat.size I.p + I.d + Nat.size I.B + Nat.size I.t + Nat.size I.aux + ⌈Q⌉₊

/-- Definition 2.2 for a family of instances `inst i` with query bounds `Q i`. One machine `tm`, one
polynomial `T` and one exponent `c` serve the whole family. For every `i`, the encoding circuit with
exponent `c` exists, and on every point `a ∈ {0,…,B}^n` the machine, started on the input word of
`inst i` and `a`, halts within `T(timeParam)` steps with the output word of a list `idx` of at most
`Q i` indices and a formula `e` that decodes at `a`. The machine sees `inst i`, never `i`. -/
def IsDatastructureFamily {ι : Type} (inst : ι → DSInstance) (Q : ι → ℝ) : Prop :=
  ∃ (tm : Turing.TM2ComputableAux Bool Bool) (T : Polynomial ℕ) (c : ℕ),
    ∀ i : ι, EncodingCircuits.{u} (inst i) c ∧
      ∀ a : Fin (inst i).n → ℕ, (∀ j, a j ≤ (inst i).B) →
        ∃ (idx : List (Fin (inst i).n → ℕ)) (e : AF ℕ) (m : ℕ),
          DecodesAt.{u} (inst i) a idx e ∧
            (idx.length : ℝ) ≤ Q i ∧
            m ≤ T.eval (timeParam (inst i) (Q i)) ∧
            HMBinPacking.OutputsWithin tm (inputWord (inst i) a)
              (outputWord (inst i) idx e) m

end PolyEvalDS.LargeChar


