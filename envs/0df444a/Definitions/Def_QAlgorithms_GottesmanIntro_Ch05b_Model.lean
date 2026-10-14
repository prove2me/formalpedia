-- Prove2me | Definitions.Def_QAlgorithms_GottesmanIntro_Ch05b_Model
-- name    : QAlgorithms_GottesmanIntro_Ch05b_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T18:04:31.759003+00:00
-- url     : https://prove2.me/theorems/8863e348-1d91-4961-9a9d-a0aefed0b027
-- title:
--   GottesmanIntro Ch05b: supporting definitions
-- statement:
--   Gottesman, *An introduction to quantum error correction*, §5.2: decoding with bad extended
--
--   ## QAlgorithms.GottesmanIntro.exRecSize
--
--   For any protocol $P$ and any location kind $\kappa$ among preparation, Hadamard, T, CNOT, measurement, and wait, this is $|P.\mathrm{gadget}(\kappa)|+(\mathrm{lead}(\kappa)+\mathrm{trail}(\kappa))|P.\mathrm{ec}|$, where the size of a location circuit is the total number of listed locations over all its steps. The leading count is $0$ for preparation and otherwise the location arity; the trailing count is $0$ for measurement and otherwise the arity; CNOT has arity $2$ and every other kind has arity $1$. Thus the error-correction size multiplier is $1$ for preparation and measurement, $4$ for CNOT, and $2$ for Hadamard, T, and wait. A protocol contains arbitrary natural parameters $n,t,A$, a complex code subspace on $n$ bits, an encoding matrix from a Boolean index, a matrix-to-matrix decoding function, six gadgets on $\mathrm{arity}(\kappa)(n+A)$ bits, an error-correction circuit on $n+A$ bits, and a Boolean decoder of lists of measurement bits; it carries no correctness hypotheses. Empty gadgets and error-correction circuits are permitted.
--
--   ## QAlgorithms.GottesmanIntro.exRecSubsetMax
--
--   For any protocol $P$ with arbitrary natural parameters $n,t,A$, code subspace, encoding matrix, matrix-to-matrix decoding function, six location-circuit gadgets, error-correction location circuit, and Boolean decoder of measurement lists, this is the maximum over the six kinds preparation, Hadamard, T, CNOT, measurement, and wait of $\binom{s_\kappa}{t+1}$, where $s_\kappa$ is the gadget's number of listed locations plus the error-correction circuit's number of listed locations multiplied by $1$ for preparation or measurement, $4$ for CNOT, and $2$ for the other kinds. The fold takes its initial maximum against $0$. The binomial coefficient is $0$ whenever $t+1>s_\kappa$, so the result is $0$ if every size is at most $t$; no protocol correctness assumptions are imposed.
--
--   ## QAlgorithms.GottesmanIntro.levelReducedBound
--
--   For any protocol $P$ (arbitrary natural parameters $n,t,A$, code subspace, encoding matrix, decoding function, six gadgets, error-correction circuit, and measurement-list decoder), any natural number $N$, any location circuit $C$ on $N$ wires, any function $p:\mathbb N\times\mathbb N\to\mathbb R$, and any index pair $\ell$, this defines $\sum_{R\subseteq E,\ |R|=t+1}\prod_{j\in R}p(j)$ as a real number. To define $E$, replace each step $s$ of $C$ by gadget layers of depth equal to the maximum of the six gadget depths, concatenating at each layer the corresponding layer of each location's gadget in listed order, and then by all layers of the error-correction circuit on each wire that participates in a nonmeasurement location of that step, with these wires ordered increasingly. Each gadget location has owner equal to the original location pair; each error-correction location has owner $(s,q)$. These lists of layers define physical index pairs (layer number, position in layer). If $\ell$ is not a listed location of $C$, set $E=\varnothing$. Otherwise, writing its step as $s_\ell$ and its wire set as $Q_\ell$, include in $E$ precisely the physical locations owned by its gadget, together with error-correction locations owned by $(s,q)$ where $q\in Q_\ell$ and either its kind is not preparation and $s+1=s_\ell$, or its kind is not measurement and $s=s_\ell$. No trailing location is truncated. If $|E|<t+1$, including an invalid $\ell$, the sum is $0$; $p$ need not be nonnegative or bounded, and no well-formedness or correctness assumption is required for $P$ or $C$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/GottesmanIntro/Ch05b.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_FTCircuit
/-!
# Gottesman, *An introduction to quantum error correction*, §5.2: decoding with bad extended
rectangles, level reduction, the threshold theorem (Theorems 8, 9, 10)

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N" (PDF pages).

Standing assumptions of the section, carried by the frozen definition layer: one
`[[n, 1, 2t + 1]]` code (p.19) with fault-tolerant gadgets for preparation, measurement, `H`,
`R_{π/8}`, CNOT, wait and error correction (Defs. 2–5, `FTProtocol.IsFaultTolerant`), gadgets of
a common depth so that `C′` is again divided into time steps (Def. 6, `FTProtocol.HasUniformDepth`);
`C` is a Def. 6 circuit with no input, every qubit prepared first and measured last
(`LocCircuit.IsIdealCircuit`); the output of `C′` is its measurement record decoded classically
by the measurement gadgets' decoding (classical computation is perfect, p.17).
-/

namespace QAlgorithms.GottesmanIntro

/-- The number of locations of a full ExRec of type `κ` (Def. 7): the gadget for `κ` plus one
leading EC per input block (none for a preparation) and one trailing EC per output block (none
for a measurement). -/
def exRecSize (P : FTProtocol) (κ : LocKind) : ℕ :=
  (P.gadget κ).size + (κ.leadCount + κ.trailCount) * P.ec.size

/-- Gottesman intro p.41, the constant `A` of eq. (85): the maximum over the types of ExRecs of
the number of sets of exactly `t + 1` locations in the ExRec. -/
def exRecSubsetMax (P : FTProtocol) : ℕ :=
  [LocKind.prep, .had, .tgate, .cnot, .meas, .wait].foldr
    (fun κ acc => max ((exRecSize P κ).choose (P.t + 1)) acc) 0

/-- Gottesman intro p.40, eq. (84): the error bound `p′_i = Σ_R Π_{j∈R} p_j` for location `ℓ` of
`C`, the sum over the sets `R` of exactly `t + 1` locations of `C′` contained in the (full) ExRec
of `ℓ`. -/
noncomputable def levelReducedBound (P : FTProtocol) {N : ℕ} (C : LocCircuit N)
    (p : ℕ × ℕ → ℝ) (ℓ : ℕ × ℕ) : ℝ :=
  ∑ R ∈ (exRecLocs P C ℓ ∅).powersetCard (P.t + 1), ∏ j ∈ R, p j




end QAlgorithms.GottesmanIntro


