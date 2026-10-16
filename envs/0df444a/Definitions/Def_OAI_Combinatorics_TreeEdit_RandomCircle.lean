-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
-- name    : OAI_Combinatorics_TreeEdit_RandomCircle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:24:04.449448+00:00
-- url     : https://prove2.me/theorems/cb759ca1-390b-4f6d-b8b2-f1697fce9ee8
-- title:
--   Finite-grid sampling of leaf phases and the row-shift vector
-- statement:
--   This file replaces continuous leaf phases by points of a finite cyclic group, so that averages over phases become finite uniform averages. Notation: $\mathbb{T}=\mathbb{R}/\mathbb{Z}$; $\mathcal{S}_h(A)$ is the group of vectors over an abelian group $A$ indexed by the leaves of the complete $m$-ary tree of height $h$ (so $\mathcal{S}_0(A)=A$ and $\mathcal{S}_{h+1}(A)=\mathcal{S}_h(A)^{m}$); $\Delta_h:A\to\mathcal{S}_h(A)$ is the diagonal map; $M\ge1$ is an integer; and $X_h(C,\omega)$ is the circle-phase tree word of a configuration $C$ (with $m=gs$ children per node, and at a node with permutation $\sigma$ the period $P_\sigma$ and child coefficients $c_i$) evaluated at a phase vector $\omega\in\mathcal{S}_h(\mathbb{T})$.
--
--   1. **Leafwise maps.** A homomorphism $f:A\to B$ induces the homomorphism $\mathcal{S}_h(f):\mathcal{S}_h(A)\to\mathcal{S}_h(B)$ applying $f$ at every leaf.
--
--   2. **Sampling.** $\operatorname{smp}_h=\mathcal{S}_h(\iota_M):\mathcal{S}_h(\mathbb{Z}/M\mathbb{Z})\to\mathcal{S}_h(\mathbb{T})$, where $\iota_M(a)=a/M \bmod 1$ identifies $\mathbb{Z}/M\mathbb{Z}$ with the $M$-point grid of the circle.
--
--   3. **Child embedding.** For $i\in\{0,\dots,m-1\}$, $\kappa_i:\mathcal{S}_h(A)\to\mathcal{S}_{h+1}(A)$ sends $v$ to the vector equal to $v$ on the subtree of child $i$ and to $0$ elsewhere.
--
--   4. **Sampled word.** For $x\in\mathcal{S}_h(\mathbb{Z}/M\mathbb{Z})$, $Y_h(C,x)=X_h\bigl(C,\operatorname{smp}_h(x)\bigr)$.
--
--   5. **Row-shift vector.** For $C\in\mathcal{C}_{h+1}$ with root permutation $\sigma$ and child coefficients $c_i$, the vector $v_C\in\mathcal{S}_{h+1}(\mathbb{Z}/M\mathbb{Z})$ has $i$-th child component
--
--      $$v_C(i)=\Delta_h\Bigl(c_i\,\bigl\lfloor M/P_\sigma\bigr\rfloor \bmod M\Bigr),$$
--
--      i.e. every leaf below child $i$ receives the residue $c_i\lfloor M/P_\sigma\rfloor$.
--
--   When $P_\sigma$ divides $M$, sampling turns $a\,v_C$ into the shift by $a c_i/P_\sigma$ of every leaf phase below child $i$, which is exactly the phase drift across $a$ rows. Adding $a\,v_C$ therefore moves every row index forward by $a$, so the node's word loses its first $a$ rows and gains $a$ new rows at the end. The finite group $\mathcal{S}_h(\mathbb{Z}/M\mathbb{Z})\cong(\mathbb{Z}/M\mathbb{Z})^{m^h}$ is the discrete torus on which the Fourier obstruction for the $\ell_1$ distortion of binary edit distance is carried out, with uniform averages over $x$ in place of Haar integrals.
--
--   **Formalization Note** The Lean names are `mapState`, `sample` (built from `ZMod.toAddCircle`, requiring `NeZero M`), `child` (an `AddMonoidHom.single`), `sampledWord` and `cycle`. In `cycle` the quotient `M / period r j C.1` is natural-number division, cast into `ZMod M`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/RandomCircle.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/RandomCircle.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation

namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

noncomputable def mapState {A B : Type} [AddCommGroup A] [AddCommGroup B] {m : ℕ}
    (f : A →+ B) : (h : ℕ) → State A m h →+ State B m h
  | 0 => f
  | h + 1 => AddMonoidHom.pi (fun i : Fin m => (mapState f h).comp (Pi.evalAddMonoidHom _ i))

noncomputable def sample {M m : ℕ} [NeZero M] (h : ℕ) : State (ZMod M) m h →+ State UnitAddCircle m h :=
  mapState ZMod.toAddCircle h

noncomputable def child {A : Type} [AddCommGroup A] {m : ℕ} (h : ℕ) (i : Fin m) :
    State A m h →+ State A m (h + 1) := AddMonoidHom.single (fun _ : Fin m => State A m h) i

noncomputable def sampledWord {I : Type} {g s L M : ℕ} [NeZero M]
    (r : I → ℕ) (j : Fin g → I) (T R : ℕ) [NeZero R]
    (h : ℕ) (C : Config I L (g * s) h) (x : State (ZMod M) (g * s) h) :=
  word r j T R h C (sample (M := M) (m := g * s) h x)

noncomputable def cycle {I : Type} {g s L M : ℕ} [NeZero M]
    (r : I → ℕ) (j : Fin g → I) (h : ℕ) (C : Config I L (g * s) (h + 1)) :
    State (ZMod M) (g * s) (h + 1) := fun i => diagonal (A := ZMod M) (m := g * s) h
      ((coefficient r j C.1 (C.2 i).1 i) • (M / period r j C.1 : ZMod M))

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

end TreeEdit.TorusTree

end OAI


