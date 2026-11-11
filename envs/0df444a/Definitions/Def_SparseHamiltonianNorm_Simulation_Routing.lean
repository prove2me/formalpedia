-- Prove2me | Definitions.Def_SparseHamiltonianNorm_Simulation_Routing
-- name    : SparseHamiltonianNorm_Simulation_Routing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:40:55.792456+00:00
-- url     : https://prove2.me/theorems/41fdff2f-969d-4721-a3d5-295b90cbb1f1
-- title:
--   Shared-history routing clock and signed reachable ladder
-- statement:
--   A horizon-$R$ routing state consists of $R$ public system slots and one shared private $L^2$ history. Initially slot $j$ contains $a_j\xi$ and the private history is zero. Slot $k$ interacts with that history using the fixed coupling and a private Cayley query; other public slots stay unchanged. Folding these interactions in increasing slot order defines the routed prefix. The public block projects the final slots against the output amplitudes $b$.
--
--   The clock cross-spectrum is
--   $$\rho_{b\leftarrow a}(\theta)=\frac{\overline{b(e^{i\theta})}\,a(e^{i\theta})}{2\pi},\qquad a(z)=\sum_j a_jz^j.$$
--   It can be complex. The reachable ladder $F_k$ is the subspace of actual $L^2$ fields $r\mapsto e^{-ar}f(r)$ with vector-polynomial degree at most $k$. Negative indices give the zero subspace. The finite completion space is the Hilbert sum of the system and $F_{R-1}$. These definitions do not assume the cross-spectral identity or the existence of a unitary completion.
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), pp.15–18, Eqs. (50)–(60); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_Coupling

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace SparseHamiltonianNorm.Simulation
open MeasureTheory
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Public slots and one shared private history. -/
abbrev RoutedState (n e R : ℕ) (t : ℝ) := (Fin R → Vec n) × History e t

/-- Eq. (51), without an autonomous clock shift. -/
def routedStep {n e R : ℕ} (d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (M : Matrix (Fin e) (Fin e) ℂ) (z : ℂ) (k : Fin R) (x : RoutedState n e R t) : RoutedState n e R t :=
  let y := coupling d Λ t V (x.1 k, z • historyLift t (cayley M) x.2)
  (Function.update x.1 k y.1, y.2)

/-- First k scheduled calls, starting with empty private history, Eqs. (50)--(52). -/
def routedPrefix {n e R : ℕ} (d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (M : Matrix (Fin e) (Fin e) ℂ) (z : ℂ) (a : Fin R → ℂ) (ξ : Vec n) (k : ℕ) : RoutedState n e R t :=
  ((List.finRange R).take k).foldl (fun x j => routedStep d Λ t V M z j x) (fun j => a j • ξ, 0)

/-- The actual prepare--route--unprepare public block, Eq. (56). -/
def clockBlock {n e R : ℕ} (d : ℕ) (Λ t : ℝ) (V : Matrix (Fin e) (Fin n) ℂ)
    (M : Matrix (Fin e) (Fin e) ℂ) (z : ℂ) (a b : Fin R → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (∑ k, conj (b k) • (routedPrefix d Λ t V M z a (QAlgorithms.ket j) R).1 k) i

def clockPolynomial {R : ℕ} (a : Fin R → ℂ) (z : ℂ) : ℂ := ∑ j, a j * z ^ j.val

/-- Complex cross-spectrum, not a probability density, Eq. (57). -/
def crossSpectrum {R : ℕ} (a b : Fin R → ℂ) (θ : ℝ) : ℂ :=
  conj (clockPolynomial b (Complex.exp ((θ : ℂ) * Complex.I))) *
    clockPolynomial a (Complex.exp ((θ : ℂ) * Complex.I)) / (2 * Real.pi)

def clockNormSq {R : ℕ} (a : Fin R → ℂ) : ℝ := ∑ j, ‖a j‖ ^ 2

/-- Actual polynomial-exponential L² subspace. Signed k retains F_{-1}={0}. -/
def historyLadder (e d : ℕ) (Λ t : ℝ) (k : ℤ) : Submodule ℂ (History e t) :=
  if k < 0 then ⊥ else Submodule.span ℂ
    {q | ∃ c : Fin (k.toNat + 1) → Vec e,
      q = historyClass t (fun r => (Real.exp (-(Real.sqrt d * Λ) * r) : ℂ) •
        ∑ j, (r : ℂ) ^ j.val • c j)}

/-- The finite reachable space with its Hilbert direct-sum norm. -/
abbrev FiniteHistorySpace (n e d : ℕ) (Λ t : ℝ) (R : ℕ) :=
  WithLp 2 (Vec n × historyLadder e d Λ t ((R : ℤ) - 1))

/-- Inclusion of the finite reachable space into the continuous orthogonal sum. -/
def finiteHistoryInclusion {n e d : ℕ} {Λ t : ℝ} {R : ℕ}
    (x : FiniteHistorySpace n e d Λ t R) : Vec n × History e t :=
  ((WithLp.ofLp x).1, (WithLp.ofLp x).2.val)

end SparseHamiltonianNorm.Simulation


