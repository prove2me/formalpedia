-- Prove2me | Definitions.Def_SuperactivatedCheating_StateConversion_QuantumGames
-- name    : SuperactivatedCheating_StateConversion_QuantumGames
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:31.269725+00:00
-- url     : https://prove2.me/theorems/fc3aba14-71c6-41a0-b14f-baf103d9efb6
-- title:
--   §2.1 — quantum games, local strategies, local value and parallel repetition
-- statement:
--   A register is a finite set and $\mathcal H_A=\mathbb C^A$. A (single-round, two-party) quantum game $G=(|\psi\rangle_{ABR},\Pi_{\rm acc})$ consists of question registers $A,B$ for Alice and Bob, a referee register $R$, answer registers $a,b$, a unit question vector $\psi\in\mathcal H_A\otimes\mathcal H_B\otimes\mathcal H_R$ and an orthogonal projection $\Pi_{\rm acc}$ (Hermitian, idempotent) on $\mathcal H_a\otimes\mathcal H_b\otimes\mathcal H_R$; the answer registers are nonempty. A local strategy $S=(\mathcal E,\mathcal F)$ is a pair of quantum channels $\mathcal E:L(\mathcal H_A)\to L(\mathcal H_a)$, $\mathcal F:L(\mathcal H_B)\to L(\mathcal H_b)$, each given by a finite normalized Kraus family of any rank; there is no shared entanglement or randomness. Its winning probability is $\omega(G;S)=\operatorname{Re}\operatorname{Tr}[\Pi_{\rm acc}(\mathcal E\otimes\mathcal F\otimes\mathrm{id}_R)(|\psi\rangle\langle\psi|)]$ and the local value is $\omega(G)=\sup_S\omega(G;S)$ over all local strategies. The $n$-fold parallel repetition $G^n$ has question state $\psi^{\otimes n}$ and accepting projection $\Pi_{\rm acc}^{\otimes n}$, with Alice holding $A_1\cdots A_n$ and answering $a_1\cdots a_n$ jointly, Bob likewise, and the referee keeping $R_1\cdots R_n$.
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/399.pdf, §2 notation, pp. 9–10, and §2.1, pp. 11–12

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel

/-!
# Single-round quantum games, local strategies, local value, parallel repetition

Bhattacharyya, Mančinska, Zhao, *Quantum interaction can superactivate cheating under parallel
repetition*, STOC 2027 submission #399 (October 2026), §2 (pp. 9–10) and §2.1 (pp. 11–12).

Registers are finite sets (p. 9); the Hilbert space of a register `A` is `ℂ^A`. Operators are
matrices indexed by the register, and a joint register `ABR` is the product type `A × B × R`.
-/

namespace SuperactivatedCheating.StateConversion

open scoped Matrix ComplexConjugate

/-- §2.1, p. 11: the data of a single-round quantum two-party game `G = (|ψ⟩_{ABR}, Π_acc)`.
`A`, `B` are the question registers of Alice and Bob, `R` the referee's register, `a`, `b` the
answer registers. `ψ` is the question state on `ABR`, `acc` the accepting operator `Π_acc` on `abR`. That
they are a unit vector and an orthogonal projection is the predicate `IsQuantumGame`. -/
structure QuantumGame (A B R a b : Type*) where
  /-- The question state `|ψ⟩_{ABR}`, as its coordinate vector. -/
  ψ : A × B × R → ℂ
  /-- The accepting operator `Π_acc` on `H_a ⊗ H_b ⊗ H_R`. -/
  acc : Matrix (a × b × R) (a × b × R) ℂ

variable {A B R a b : Type*} [Fintype A] [Fintype B] [Fintype R] [Fintype a] [Fintype b]
  [DecidableEq A] [DecidableEq B] [DecidableEq R] [DecidableEq a] [DecidableEq b]

/-- §2.1, p. 11 and §2, p. 10: `G` is a quantum game: `ψ` is a unit vector, `Π_acc` is an
orthogonal projection (Hermitian and idempotent), and the answer registers are nonempty sets
(every register carries density operators, p. 10; the question registers are nonempty because `ψ`
is a unit vector). -/
def IsQuantumGame (G : QuantumGame A B R a b) : Prop :=
  ∑ x, ‖G.ψ x‖ ^ 2 = 1 ∧ G.accᴴ = G.acc ∧ G.acc * G.acc = G.acc ∧ Nonempty a ∧ Nonempty b

/-- §2.1, p. 11: a local (unassisted) strategy `S = (E, F)`: quantum channels
`E : L(H_A) → L(H_a)` and `F : L(H_B) → L(H_b)`, each given by a finite normalized Kraus family
(of any finite rank). There is no shared entanglement and no shared randomness. -/
structure LocalStrategy (A B a b : Type*) [Fintype a] [Fintype b] [DecidableEq A]
    [DecidableEq B] where
  /-- Kraus rank of Alice's channel. -/
  mA : ℕ
  /-- Kraus rank of Bob's channel. -/
  mB : ℕ
  /-- Alice's Kraus operators `H_A → H_a`. -/
  E : Fin mA → Matrix a A ℂ
  /-- Bob's Kraus operators `H_B → H_b`. -/
  F : Fin mB → Matrix b B ℂ
  isKraus_E : QAlgorithms.IsKrausFamily E
  isKraus_F : QAlgorithms.IsKrausFamily F

/-- The operator `K ⊗ L ⊗ I_R : H_A ⊗ H_B ⊗ H_R → H_a ⊗ H_b ⊗ H_R`. -/
def tensorKraus (R : Type*) [DecidableEq R] (K : Matrix a A ℂ) (L : Matrix b B ℂ) :
    Matrix (a × b × R) (A × B × R) ℂ :=
  Matrix.of fun o i => K o.1 i.1 * L o.2.1 i.2.1 * if o.2.2 = i.2.2 then 1 else 0

/-- The pure state `|ψ⟩⟨ψ|`. -/
def pureState {ι : Type*} (ψ : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ψ i * conj (ψ j)

/-- §2.1, p. 11: the returned state `(E ⊗ F ⊗ id_R)(|ψ⟩⟨ψ|)` on `abR`, with the Kraus family
`{E_j ⊗ F_k ⊗ I_R}_{j,k}` of the product channel. -/
noncomputable def outputState (ψ : A × B × R → ℂ) (S : LocalStrategy A B a b) :
    Matrix (a × b × R) (a × b × R) ℂ :=
  QAlgorithms.krausApply (fun jk : Fin S.mA × Fin S.mB => tensorKraus R (S.E jk.1) (S.F jk.2))
    (pureState ψ)

/-- §2.1, p. 11: the winning probability `ω(G; S) = Tr[Π_acc (E ⊗ F ⊗ id_R)(|ψ⟩⟨ψ|)]`, as the
real part of the trace (the trace is real and in `[0, 1]` for a game and a strategy). -/
noncomputable def winProb (G : QuantumGame A B R a b) (S : LocalStrategy A B a b) : ℝ :=
  (Matrix.trace (G.acc * outputState G.ψ S)).re

/-- §2.1, p. 11: the local value `ω(G) := sup{ω(G; S) : S is a local strategy}`, the supremum over
all local strategies (all finite Kraus ranks). Nothing about attainment is built in. -/
noncomputable def localValue (G : QuantumGame A B R a b) : ℝ :=
  sSup (Set.range fun S : LocalStrategy A B a b => winProb G S)

/-- §2.1, p. 12 ("Parallel repetition"): the `n`-fold parallel repetition
`Gⁿ = (|ψ⟩^{⊗n}, Π_acc^{⊗n})`. Alice receives all her question registers `A₁ … A_n` and answers
`a₁ … a_n` jointly, Bob likewise, and the referee keeps `R₁ … R_n`: the `n` copies of `ABR` are
regrouped as `(A₁…A_n)(B₁…B_n)(R₁…R_n)`, i.e. `(Fin n → A) × (Fin n → B) × (Fin n → R)`. -/
def QuantumGame.rep (G : QuantumGame A B R a b) (n : ℕ) :
    QuantumGame (Fin n → A) (Fin n → B) (Fin n → R) (Fin n → a) (Fin n → b) where
  ψ x := ∏ i, G.ψ (x.1 i, x.2.1 i, x.2.2 i)
  acc o o' := ∏ i, G.acc (o.1 i, o.2.1 i, o.2.2 i) (o'.1 i, o'.2.1 i, o'.2.2 i)

/-! ### Sanity checks -/

/-- The repetition carries the product question state. -/
example (G : QuantumGame A B R a b) (n : ℕ) (x : (Fin n → A) × (Fin n → B) × (Fin n → R)) :
    (G.rep n).ψ x = ∏ i, G.ψ (x.1 i, x.2.1 i, x.2.2 i) := rfl

/-- The identity strategy exists when questions and answers coincide. -/
example : LocalStrategy A B A B :=
  ⟨1, 1, fun _ => 1, fun _ => 1, by simp [QAlgorithms.IsKrausFamily],
    by simp [QAlgorithms.IsKrausFamily]⟩

end SuperactivatedCheating.StateConversion


