-- Prove2me | Definitions.Def_InfoLossLAR_WorstCase_QPT
-- name    : InfoLossLAR_WorstCase_QPT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:03:18.354504+00:00
-- url     : https://prove2.me/theorems/7a88ccf6-ee19-42ff-bf28-faeb555e9080
-- title:
--   Uniform QPT algorithms on classical inputs, one-call reductions, uniform PPT samplers
-- statement:
--   A **uniform QPT algorithm** with one output bit is a circuit family $F$ of the published layer `QAlgorithms.Complexity`: for each input length $n$ a layered circuit over the gate set $\{H,S,T,X,\mathrm{CNOT}\}$ on $n+(a(n)+1)$ wires with a designated output wire, generated from $1^n$ by one classical polynomial-time map (`Uniform`), with disjoint gates in every layer (`WellFormed`) and polynomially many layers and ancillas (`PolyBounded`). On a classical input $w\in\{0,1\}^n$ the circuit is applied to $|w\rangle|0\cdots0\rangle$ and all wires are measured; the acceptance probability is the Born-rule probability that the output wire reads $1$:
--   $$\Pr[F(w)=1]=\sum_{y:\,y_{\mathrm{out}}=1}\big|\langle y|\,C_n\,|w,0\cdots0\rangle\big|^2 .$$
--   A **multi-output** uniform QPT algorithm has in addition a polynomially bounded list of output wires; its output string is the measured values on these wires, and $\Pr[F(w)\in E]$ is the Born-rule probability of the event $E$ on the output string.
--
--   $B$ **calls $D$ once on a classically prepared input** if there are classical polynomial-time maps $\mathrm{pre},\mathrm{post}$ and a polynomial $m$ such that for every input $w$, $\Pr[B(w)=1]$ equals the probability of: draw $m(|w|)$ uniform coins $\rho$, run $D$ once on $\mathrm{pre}(\rho,w)$ getting a bit $b$, output the first bit of $\mathrm{post}(\rho,w,b)$.
--
--   A **uniform classical PPT sampler** of integer affine data reads the code of $(1^\lambda,\mathrm{pp})$ and $m(\lambda)$ uniform coins $\rho$ and outputs $S_\lambda(\rho)=(Q,\beta)\in\mathbb Z^{d\times d}\times\mathbb Z^d$: one classical polynomial-time map sends the code of $(\rho,(1^\lambda,\mathrm{pp}))$ to the code of $(Q,\beta)$.
--
--   **Formalization Note.** The paper names no machine model; this is the fixed universal gate set, uniform polynomial-time generation, no advice. Classical polynomial time is `QAlgorithms.Complexity.PolyTimeComputable` (multi-stack Turing machines).
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 20 §3.1 and Definition 3.7; p. 22 Theorem 4.2; p. 23 Definition 5.1; p. 60 §10.1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_InfoLossLAR_WorstCase_Encoding

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

/-!
# Uniform QPT algorithms on classical inputs, and uniform classical PPT samplers

Chen Qian, *Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices*,
arXiv:2611.05136 (held version, sha256 2ebdfbf3…), §3.1, p. 20 (Definition 3.7: "a uniform QPT
distinguisher D on classical inputs"), §4, p. 22 (Theorem 4.2: "a uniform QPT distinguisher B
using t input blocks and one call to D"), Definition 5.1, p. 23 ("uniform classical PPT
algorithms"), §10.1, p. 60 ("uniform quantum polynomial-time algorithms").

The paper names no circuit model. A **uniform QPT algorithm** is read as a circuit family of the
published `QAlgorithms.Complexity` layer: layered circuits over the fixed gate set
`{H, S, T, X, CNOT}` (Clifford+T), one circuit per input length, generated from `1^n` by a
classical polynomial-time map (`Uniform`), with disjoint gates in each layer (`WellFormed`) and
polynomially many layers and ancillas (`PolyBounded`). No advice, no other gates. A classical
input `w ∈ {0,1}^n` is loaded as the computational basis state `|w⟩|0…0⟩`; the output is the
computational-basis measurement of the designated output wire(s), with Born-rule probabilities.
-/

/-- The computational basis state `|x⟩|0^{a+1}⟩` on `n + (a + 1)` wires. -/
def basisInput {n a : ℕ} (x : Bits n) : QState (n + (a + 1)) :=
  fun y => if (∀ i : Fin n, y (Fin.castAdd (a + 1) i) = x i) ∧
      (∀ l : Fin (a + 1), y (Fin.natAdd n l) = false) then 1 else 0

/-- The probability that the circuit family `F`, run on the classical input `w`, outputs `1`:
the Born-rule probability that measuring all wires of `F.circ |w|` applied to `|w⟩|0…0⟩` gives
`1` on the output wire. -/
noncomputable def acceptProb (F : Family) (w : Str) : ℝ :=
  ∑ y : Bits (w.length + (F.anc w.length + 1)),
    if y (F.out w.length) then
      ‖runLayered (F.circ w.length) (basisInput (toBits w)) y‖ ^ 2 else 0

/-- A uniform QPT algorithm with a one-bit output (a distinguisher or a decision algorithm). -/
def IsQPT (F : Family) : Prop := Uniform F ∧ WellFormed F ∧ PolyBounded F

/-- A quantum circuit family with a multi-bit classical output: at input length `n`, `anc n`
ancillas beyond a mandatory first one, a layered circuit, and a list of `outLen n` output wires
whose measured values, in order, form the output string. -/
structure MFamily where
  /-- Number of ancilla wires at input length `n`, beyond a mandatory first one. -/
  anc : ℕ → ℕ
  /-- The circuit at input length `n`. -/
  circ : (n : ℕ) → Layered (n + (anc n + 1))
  /-- Number of output bits at input length `n`. -/
  outLen : ℕ → ℕ
  /-- The output wires at input length `n`, in order. -/
  outW : (n : ℕ) → Fin (outLen n) → Fin (n + (anc n + 1))

/-- Code of an `MFamily` at input length `n`: ancilla count, output wires, circuit. -/
def MFamily.encAt (F : MFamily) (n : ℕ) : Str :=
  encNat (F.anc n) ++ encStr ((List.ofFn (F.outW n)).map fun i => encNat (i : ℕ)) ++
    encCirc (F.circ n)

/-- A uniform QPT algorithm with a multi-bit output: the circuit at each input length is
generated from `1^n` by a classical polynomial-time map, layers act on disjoint wires, and one
polynomial bounds the depth, the ancilla count and the number of output bits. -/
def IsMQPT (F : MFamily) : Prop :=
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ n : ℕ, f (unary n) = F.encAt n) ∧
  (∀ n : ℕ, ∀ l ∈ F.circ n, LayerOk l) ∧
  ∃ p : Polynomial ℕ, ∀ n : ℕ,
    depth (F.circ n) ≤ p.eval n ∧ F.anc n ≤ p.eval n ∧ F.outLen n ≤ p.eval n

/-- The probability that the output string of `F` on the classical input `w` satisfies `E`
(Born rule, measurement of all wires, output read off the output wires in order). -/
noncomputable def outputProb (F : MFamily) (w : Str) (E : Str → Prop) : ℝ :=
  open Classical in
  ∑ y : Bits (w.length + (F.anc w.length + 1)),
    if E (List.ofFn fun j => y (F.outW w.length j)) then
      ‖runLayered (F.circ w.length) (basisInput (toBits w)) y‖ ^ 2 else 0

/-- The uniform average of a real function over a finite type. -/
noncomputable def avg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / (Fintype.card α : ℝ)

/-- **One call to `D` on a classically prepared input.** The acceptance probability of `B` on
every input `w` is that of the following procedure: draw `m(|w|)` uniform coin bits `ρ`,
compute the classical string `x = pre(ρ, w)`, run `D` once on `x` obtaining a bit `b`, and output
the first bit of `post(ρ, w, b)`; `pre` and `post` are classical polynomial-time maps and `m` a
polynomial. (Theorems 4.2, 5.4 and Corollary 5.5: "using t input blocks and one call to D".) -/
def CallsOnce (B D : Family) : Prop :=
  ∃ (pre post : Str → Str) (m : Polynomial ℕ),
    PolyTimeComputable pre ∧ PolyTimeComputable post ∧
    ∀ w : Str, acceptProb B w =
      avg fun ρ : Fin (m.eval w.length) → Bool =>
        let x := pre (encPair (List.ofFn ρ) w)
        (if (post (encPair (List.ofFn ρ) w ++ [true])).head? = some true then
            acceptProb D x else 0) +
        (if (post (encPair (List.ofFn ρ) w ++ [false])).head? = some true then
            1 - acceptProb D x else 0)

/-- **Uniform classical PPT sampler of integer affine data** (Definitions 5.1, 5.3). On input
`input λ` (the code of `(1^λ, pp)`) and `m(λ)` uniform coin bits `ρ`, the sampler outputs the
integer pair `S λ ρ = (Q, β) ∈ ℤ^{d×d} × ℤ^d`: one classical polynomial-time map `g` sends the code
of `(ρ, input λ)` to the code of `(Q, β)`. The sampler reads nothing but `1^λ`, `pp` and its
coins (source independence). -/
def IsPPTAffineSampler (input : ℕ → Str) (d : ℕ → ℕ) (m : Polynomial ℕ)
    (S : (lam : ℕ) → (Fin (m.eval lam) → Bool) →
      Matrix (Fin (d lam)) (Fin (d lam)) ℤ × (Fin (d lam) → ℤ)) : Prop :=
  ∃ g : Str → Str, PolyTimeComputable g ∧
    ∀ (lam : ℕ) (ρ : Fin (m.eval lam) → Bool),
      g (encPair (List.ofFn ρ) (input lam)) =
        encPair (encMat encI (S lam ρ).1) (encVec encI (S lam ρ).2)

end InfoLossLAR.WorstCase


