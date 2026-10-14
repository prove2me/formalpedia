-- Prove2me | Definitions.Def_QAlgorithms_Nannicini_Ch05a_Model
-- name    : QAlgorithms_Nannicini_Ch05a_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:45:02.827223+00:00
-- url     : https://prove2.me/theorems/33fcc73b-8b53-446a-a4dc-a9dedf8575a0
-- title:
--   Nannicini Ch05a: supporting definitions
-- statement:
--   Nannicini, Chapter 5 (part a): the quantum gradient algorithm and state tomography
--
--   ## QAlgorithms.Nannicini.liftPoint
--
--   For every natural number $m$, real Euclidean vector $y$ with $m$ coordinates, and real number $t$, this is the real Euclidean vector with $m+1$ coordinates obtained by keeping $y$ in the first $m$ positions and placing $t$ last. When $m=0$, it is the one-coordinate vector $(t)$.
--
--   ## QAlgorithms.Nannicini.heightFunction
--
--   For every natural number $m$, arbitrary set $K$ in real Euclidean space of dimension $m+1$, and real vector $y$ with $m$ coordinates, this is the infimum in the extended real line of all real $t$ for which appending $t$ to $y$ gives a vector in $K$. It equals $+\infty$ for an empty such set and $-\infty$ for a set unbounded below; no nonemptiness, convexity, boundedness, or attainment hypothesis is imposed.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Nannicini/Ch05a.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_GradientMethods
/-!
# Nannicini, Chapter 5 (part a): the quantum gradient algorithm and state tomography

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages): Proposition 5.3 (p.106–108), Proposition 5.6 (p.109–111), Proposition 5.16
(p.115), Corollary 5.18 (p.116–117), and Proposition 5.25 (p.120–121) as a corrected statement (see its docstring).

Conventions. A collection of `d` registers of `q` qubits each is indexed by `Fin d → Qubits q`
(register `i` is the source's register `i + 1`); a `q`-bit string is read as an integer most
significant bit first (`bitsToNat`). The binary oracle of Def. 5.1 is the frozen `modAddOracle`,
Jordan's circuit (Fig. 5.1) is the frozen `jordanGradientState`, Alg. 3 is the frozen
`gradientAlgState`, the grid `G_q` is `gridPoint`, Fig. 5.3 is the frozen `hadamardTestCircuit`,
and Def. 5.9 is the frozen `IsProbabilityOracle`.
-/

namespace QAlgorithms.Nannicini





/-- Nannicini p.120, §5.1.4: the point `(y, t) ∈ ℝ^d` with `y ∈ ℝ^{d−1}` its first `d − 1`
coordinates and `t` its last coordinate (`d = m + 1`). Chunk-local: used only by Prop. 5.25. -/
noncomputable def liftPoint {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.snoc (WithLp.ofLp y) t : Fin (m + 1) → ℝ)

/-- Nannicini p.120, the height function `h : ℝ^{d−1} → ℝ ∪ {∞}`, `h(y) := inf_{(y,t) ∈ K} t`,
"it is ∞ if no such value exists". Computed in `EReal`, so the infimum of the empty set is `⊤ = ∞`
as in the source (trap 20). Chunk-local: used only by Prop. 5.25. -/
noncomputable def heightFunction {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin (m + 1))))
    (y : EuclideanSpace ℝ (Fin m)) : EReal :=
  sInf ((fun t : ℝ => (t : EReal)) '' {t | liftPoint y t ∈ K})


end QAlgorithms.Nannicini


