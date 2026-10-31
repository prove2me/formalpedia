-- Prove2me | Definitions.Def_BlumRivest_Training_Model
-- name    : BlumRivest_Training_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:41:30.161982+00:00
-- url     : https://prove2.me/theorems/510e6985-9ac5-4d3e-938a-06dd7eeec387
-- title:
--   Definition 1 and Figure 1 — three-node networks and exact training feasibility
-- statement:
--   A network with $n$ Boolean inputs has exactly two hidden linear threshold nodes. Both receive all $n$ inputs. A third, independently trainable linear threshold node receives the two hidden outputs, numerically interpreted as −1 and +1. Every node uses the strict threshold convention. There are no other connections.
--
--   An instance consists of a dimension $n\in\mathbb N$ and a finite list $D$ of examples $(x,y)$ with $x\in\{0,1\}^n$ and $y\in\{-1,+1\}$. For network $N$, consistency means
--
--   $$\forall (x,y)\in D,\quad N(x)=y.$$
--
--   The instance is trainable exactly when some choice of all real weights and thresholds is consistent. Feasibility is not defined through a certificate bound, a reduction, or a promise of realizability. Empty lists are feasible; identical repeated pairs impose the same condition, and conflicting labels on the same input cannot both be met. Dimension zero is included and supplies the unique empty input vector.
--
--   Finite lists encode the source's finite training data; coordinates and hidden nodes use zero-based finite indices. Boolean labels encode the two source labels without admitting a third output.
-- source:
--   Blum and Rivest (1992), Definition 1, printed p. 118 (PDF p. 2), and Section 2 / Figure 1, printed p. 119 (PDF p. 3), DOI 10.1016/S0893-6080(05)80010-3.

import Definitions.Def_BlumRivest_Training_Thresholds

namespace BlumRivest.Training

/-- Two hidden threshold nodes, followed by one trainable threshold node. -/
structure Network (n : ℕ) where
  hidden : Fin 2 → Threshold n
  output : Threshold 2

/-- Hidden inputs are 0/1; the final node receives numerical -1/+1 outputs. -/
noncomputable def Network.eval {n : ℕ} (N : Network n) (x : Fin n → Bool) : Bool :=
  N.output.eval (fun j => signValue ((N.hidden j).eval (fun i => bitValue (x i))))

/-- One explicit finite training instance; the input dimension varies between instances. -/
structure Instance where
  dim : ℕ
  examples : List ((Fin dim → Bool) × Bool)

/-- Exact agreement on every supplied example. -/
def Consistent (I : Instance) (N : Network I.dim) : Prop :=
  ∀ e ∈ I.examples, N.eval e.1 = e.2

/-- Feasibility quantifies over all real network parameters, not finite certificates. -/
def Trainable (I : Instance) : Prop :=
  ∃ N : Network I.dim, Consistent I N

end BlumRivest.Training


