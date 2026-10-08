-- Prove2me | Definitions.Def_OCB2012_defs
-- name    : OCB2012_defs
-- status  : Definition
-- author  : @Alien60
-- created : 2026-10-07T23:07:32.56569+00:00
-- url     : https://prove2.me/theorems/d3e56090-6ac4-44c4-8f8a-ec5340815a11
-- title:
--   Process matrices, local instruments, causal separability and the qubit protocol (OCB 2012)
-- statement:
--   Shared vocabulary of the mission. For finite-dimensional systems $A_1,A_2,B_1,B_2$ with operators on $A_1A_2B_1B_2$ indexed in that order: the partial trace $\operatorname{Tr}_2$; CJ matrices of CPTP maps ($M\ge0$, $\operatorname{Tr}_{X_2}M=\mathbb 1^{X_1}$, p. 4); the probability rule $\operatorname{Tr}[W(M^A\otimes M^B)]$ (Eq. (3)); **process matrices** (Eqs. (4)–(5)); Alice's and Bob's local instruments with input bits $a$ and $(b,b')$ and guesses $x,y$; the success probability $p_{succ}$ of Eq. (1) (real parts of traces, bits as Booleans); the one-way forms $\mathbb 1^{A_2}\otimes W^{A_1B_1B_2}$ ($A\not\preceq B$) and $\mathbb 1^{B_2}\otimes W^{A_1A_2B_1}$ ($B\not\preceq A$); **causal separability** (Eq. (6)); the Pauli matrices, the process matrix $W$ of Eq. (7), Alice's instrument $\xi$ (Eq. (20)) and Bob's $\eta$ (Eqs. (21)–(23), with Bob's prepared state $\rho^{B_2}$ as a parameter); Hilbert–Schmidt bases (Appendix C) and the allowed term types of Fig. 3.
-- source:
--   O. Oreshkov, F. Costa, Č. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, pp. 2–5 Eqs. (1), (3)–(7); Appendix C; Appendix E Eqs. (20)–(23); Fig. 3

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

/-!
# Process matrices and the causal inequality

Definitions for the mission drafted from O. Oreshkov, F. Costa and Č. Brukner,
*Quantum correlations with no causal order*, Nat. Commun. 3, 1092 (2012),
arXiv:1105.4464v3.

Alice has an input system `A1` and an output system `A2`; Bob has `B1` and `B2`.
All systems are finite-dimensional and indexed by finite types `a1 a2 b1 b2`.
Bipartite operators on `A1A2B1B2` are matrices indexed by `(a1 × a2) × (b1 × b2)`,
so that `MA ⊗ₖ MB` is `M^{A1A2} ⊗ M^{B1B2}` in the order used by the paper.
Local operations are represented directly by their Choi–Jamiołkowski (CJ) matrices.
-/

namespace OCB2012

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

/-- Partial trace over the second tensor factor:
`(Tr₂ M)_{ij} = ∑ₖ M_{(i,k),(j,k)}`. -/
def ptrace₂ {α β : Type*} [Fintype β] (M : Matrix (α × β) (α × β) ℂ) : Matrix α α ℂ :=
  Matrix.of fun i j => ∑ k, M (i, k) (j, k)

/-- p. 4: the CJ matrix `M^{X1X2}` of a completely positive trace-preserving map from
`X1` to `X2` is characterized by `M ≥ 0` and `Tr_{X2} M = 𝟙^{X1}`. -/
def IsCPTP_CJ {x1 x2 : Type*} [Fintype x1] [Fintype x2] [DecidableEq x1]
    (M : Matrix (x1 × x2) (x1 × x2) ℂ) : Prop :=
  M.PosSemidef ∧ ptrace₂ M = 1

/-- Eq. (3): the probability `Tr[W (M^{A1A2} ⊗ M^{B1B2})]` of the pair of local
outcomes with CJ matrices `MA`, `MB`. -/
def prob {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2] [Fintype b1] [Fintype b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ) : ℂ :=
  (W * (MA ⊗ₖ MB)).trace

/-- Eqs. (4)–(5): `W` is a **process matrix** if `W ≥ 0` and
`Tr[W (M^{A1A2} ⊗ M^{B1B2})] = 1` for all CJ matrices of CPTP maps. -/
def IsProcessMatrix {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2] [Fintype b1]
    [Fintype b2] [DecidableEq a1] [DecidableEq b1]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) : Prop :=
  W.PosSemidef ∧
    ∀ (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ),
      IsCPTP_CJ MA → IsCPTP_CJ MB → prob W MA MB = 1

/-- Alice's local quantum instrument in the task of Eq. (1): for each input bit `a`
a family of CJ matrices `MA x a ≥ 0` indexed by her guess `x`, whose sum over `x`
is the CJ matrix of a CPTP map. -/
def IsAliceInstrument {a1 a2 : Type*} [Fintype a1] [Fintype a2] [DecidableEq a1]
    (MA : Bool → Bool → Matrix (a1 × a2) (a1 × a2) ℂ) : Prop :=
  (∀ x a, (MA x a).PosSemidef) ∧ ∀ a, IsCPTP_CJ (∑ x, MA x a)

/-- Bob's local quantum instrument in the task of Eq. (1): for each pair of input bits
`b, b'` a family of CJ matrices `MB y b b' ≥ 0` indexed by his guess `y`, whose sum
over `y` is the CJ matrix of a CPTP map. -/
def IsBobInstrument {b1 b2 : Type*} [Fintype b1] [Fintype b2] [DecidableEq b1]
    (MB : Bool → Bool → Bool → Matrix (b1 × b2) (b1 × b2) ℂ) : Prop :=
  (∀ y b b', (MB y b b').PosSemidef) ∧ ∀ b b', IsCPTP_CJ (∑ y, MB y b b')

/-- Eq. (1): the probability of success
`p_succ = ½ [P(x = b | b' = 0) + P(y = a | b' = 1)]`, with `a, b, b'` independent and
uniformly distributed. Bits are encoded as `Bool` (`false ↦ 0`, `true ↦ 1`), and the
joint probability of guesses `x, y` given inputs `a, b, b'` is
`Tr[W (MA x a ⊗ MB y b b')]` (Eq. (3)). Probabilities are the real parts of these traces. -/
def pSucc {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2] [Fintype b1] [Fintype b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (MA : Bool → Bool → Matrix (a1 × a2) (a1 × a2) ℂ)
    (MB : Bool → Bool → Bool → Matrix (b1 × b2) (b1 × b2) ℂ) : ℝ :=
  (1 / 2 : ℝ) * ((1 / 4 : ℝ) * ∑ a : Bool, ∑ b : Bool, ∑ y : Bool,
      (prob W (MA b a) (MB y b false)).re) +
  (1 / 2 : ℝ) * ((1 / 4 : ℝ) * ∑ a : Bool, ∑ b : Bool, ∑ x : Bool,
      (prob W (MA x a) (MB a b true)).re)

/-- p. 4: `W` has the form `𝟙^{A2} ⊗ W^{A1B1B2}` (a channel with memory from Bob to
Alice; no signalling from Alice to Bob, written `A ⋠ B`). -/
def IsNoSignalAtoB {a1 a2 b1 b2 : Type*} [DecidableEq a2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) : Prop :=
  ∃ X : Matrix (a1 × (b1 × b2)) (a1 × (b1 × b2)) ℂ,
    W = Matrix.of fun r c => if r.1.2 = c.1.2 then X (r.1.1, r.2) (c.1.1, c.2) else 0

/-- p. 4: `W` has the form `𝟙^{B2} ⊗ W^{A1A2B1}` (no signalling from Bob to Alice,
written `B ⋠ A`). -/
def IsNoSignalBtoA {a1 a2 b1 b2 : Type*} [DecidableEq b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) : Prop :=
  ∃ X : Matrix ((a1 × a2) × b1) ((a1 × a2) × b1) ℂ,
    W = Matrix.of fun r c => if r.2.2 = c.2.2 then X (r.1, r.2.1) (c.1, c.2.1) else 0

/-- Eq. (6): `W` is **causally separable** if `W = q W^{B⋠A} + (1 - q) W^{A⋠B}` for some
`0 ≤ q ≤ 1`, where `W^{B⋠A}` and `W^{A⋠B}` are process matrices of the respective
no-signalling forms. -/
def IsCausallySeparable {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2] [Fintype b1]
    [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) : Prop :=
  ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
    ∃ WBA WAB : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ,
      IsProcessMatrix WBA ∧ IsNoSignalBtoA WBA ∧
      IsProcessMatrix WAB ∧ IsNoSignalAtoB WAB ∧
      W = (q : ℂ) • WBA + ((1 - q : ℝ) : ℂ) • WAB

/-! ### The qubit example (Eq. (7)) and the protocol of Appendix E -/

/-- A two-level system. -/
abbrev Qubit := Fin 2

/-- Pauli matrix `σ_x`. -/
def σx : Matrix Qubit Qubit ℂ := !![0, 1; 1, 0]

/-- Pauli matrix `σ_z` (`|z₊⟩ = |0⟩`, `|z₋⟩ = |1⟩`). -/
def σz : Matrix Qubit Qubit ℂ := !![1, 0; 0, -1]

/-- `(-1)^x` for a bit `x`. -/
def sgn (x : Bool) : ℂ := if x then -1 else 1

/-- Eq. (7): the process matrix
`W = ¼ [𝟙 + (1/√2)(σ_z^{A2} σ_z^{B1} + σ_z^{A1} σ_x^{B1} σ_z^{B2})]`
on four qubits `A1 A2 B1 B2`. -/
def W7 : Matrix ((Qubit × Qubit) × (Qubit × Qubit)) ((Qubit × Qubit) × (Qubit × Qubit)) ℂ :=
  (1 / 4 : ℂ) • (1 + ((1 / Real.sqrt 2 : ℝ) : ℂ) •
    ((((1 : Matrix Qubit Qubit ℂ) ⊗ₖ σz) ⊗ₖ (σz ⊗ₖ (1 : Matrix Qubit Qubit ℂ))) +
     ((σz ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) ⊗ₖ (σx ⊗ₖ σz))))

/-- Eq. (20): Alice's CJ matrices `ξ(x, a) = ¼ [𝟙 + (-1)^x σ_z]^{A1} ⊗ [𝟙 + (-1)^a σ_z]^{A2}`
(measure the incoming qubit in the `z` basis, record `x`, re-prepare `a` in the `z` basis). -/
def ξ (x a : Bool) : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ :=
  (1 / 4 : ℂ) • ((1 + sgn x • σz) ⊗ₖ (1 + sgn a • σz))

/-- Eqs. (21)–(23): Bob's CJ matrices `η(y, b, b') = b' η₁(y, b) + (b' ⊕ 1) η₂(y, b)` with
`η₁(y, b) = ½ [𝟙 + (-1)^y σ_z]^{B1} ⊗ ρ^{B2}` and
`η₂(y, b) = ¼ [𝟙 + (-1)^y σ_x]^{B1} ⊗ [𝟙 + (-1)^{b+y} σ_z]^{B2}`,
where `ρ` is the arbitrary state Bob prepares when `b' = 1`. -/
def η (ρ : Matrix Qubit Qubit ℂ) (y b b' : Bool) : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ :=
  if b' then (1 / 2 : ℂ) • ((1 + sgn y • σz) ⊗ₖ ρ)
  else (1 / 4 : ℂ) • ((1 + sgn y • σx) ⊗ₖ (1 + sgn (xor b y) • σz))

/-! ### Hilbert–Schmidt bases (Appendix C) -/

/-- Appendix C: a Hilbert–Schmidt basis `{σ_μ}_{μ=0}^{d²-1}` of the operators on `ℂ^X`,
with `σ₀ = 𝟙` and the remaining elements `τ j` Hermitian, traceless, and orthogonal:
`Tr σ_μ σ_ν = d δ_{μν}`, where `d = |X|`. -/
structure HSBasis (X : Type*) [Fintype X] [DecidableEq X] where
  /-- Index type of the non-identity elements. -/
  ι : Type
  [instFintype : Fintype ι]
  [instDecEq : DecidableEq ι]
  /-- The non-identity basis elements `σ_j`, `j = 1, …, d² - 1`. -/
  τ : ι → Matrix X X ℂ
  isHermitian : ∀ j, (τ j).IsHermitian
  trace_eq_zero : ∀ j, (τ j).trace = 0
  trace_mul : ∀ i j, (τ i * τ j).trace = if i = j then (Fintype.card X : ℂ) else 0
  card_eq : Fintype.card ι + 1 = Fintype.card X ^ 2

attribute [instance] HSBasis.instFintype HSBasis.instDecEq

/-- The full basis `σ_μ`, with `none ↦ σ₀ = 𝟙` and `some j ↦ σ_j`. -/
def HSBasis.σ {X : Type*} [Fintype X] [DecidableEq X] (B : HSBasis X) :
    Option B.ι → Matrix X X ℂ
  | none => 1
  | some j => B.τ j

/-- Fig. 3 / Appendix C: a Hilbert–Schmidt term `σ_μ^{A1} σ_ν^{A2} σ_λ^{B1} σ_γ^{B2}` is of an
**allowed type** if its set of non-identity factors is one of `∅, A1, B1, A1B1, A2B1,
A1A2B1, A1B2, A1B1B2`; equivalently, a non-identity factor on `A2` requires one on `B1`
and none on `B2`, and a non-identity factor on `B2` requires one on `A1` and none on `A2`. -/
def AllowedType (μ ν l γ : Bool) : Prop :=
  (ν → l ∧ ¬γ) ∧ (γ → μ ∧ ¬ν)

end

end OCB2012


