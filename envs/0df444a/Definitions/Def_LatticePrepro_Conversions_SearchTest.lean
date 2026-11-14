-- Prove2me | Definitions.Def_LatticePrepro_Conversions_SearchTest
-- name    : LatticePrepro_Conversions_SearchTest
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:24:30.298057+00:00
-- url     : https://prove2.me/theorems/0c9e3512-5715-4874-aa78-0ebb8574f293
-- title:
--   The search test of Lemma 5.2: acceptance and $f$-approximate solutions for codes and lattices
-- statement:
--   Lemma 5.2 tests a vector returned by a search algorithm: it must lie in the code or lattice, and its residual weight must be at most the gap times the radius. These definitions express the test and approximate solutions as predicates.
--
--   **Codes.** For a code family $(\mathcal C,(t_x)_{x\in X})$ over a field $F$ (`CodeFamily`), with $\Delta$ the Hamming distance:
--   - `CodeFamily.Accepts g R x c` (for $g,R\in\mathbb N$): $c\in\mathcal C$ and $\Delta(t_x,c)\le g\cdot R$.
--   - `CodeFamily.IsApprox f x c` (for real $f$): $c$ is an $f$-approximate solution, i.e. $c\in\mathcal C$ and $\Delta(t_x,c)\le f\cdot\Delta(t_x,\mathcal C)$.
--
--   **Lattices.** For a lattice reduction `Red : LatticeReduction L g pn` with lattice $\Lambda\subseteq\mathbb Z^M$, targets $t_x$, residual weight $w$, $D$ blocks and norm exponent $p$:
--   - `LatticeReduction.Accepts x v`: $v\in\Lambda$ and $w(x,v)\le g\cdot D$.
--   - `LatticeReduction.IsApprox f x v`: $v\in\Lambda$ and $\|t_x-v\|_p\le f\cdot\operatorname{dist}_p(t_x,\Lambda)$, where $\operatorname{dist}_p(t_x,\Lambda)=\min_{u\in\Lambda}\|t_x-u\|_p$ (Definition 3.1).
--
--   In the proof of Lemma 5.2, the code test uses the residual weight $\Delta(t_x,c)$ and the threshold $\Gamma\cdot D$ (radius $R=D$); the lattice test uses the residual weight of Lemma 3.12 with the same threshold.
--
--   **Formalization Note.** The test is a proposition, not an algorithm; the paper's claim that it runs in polynomial time is not formalized. For codes the threshold is written $g\cdot R$ with an arbitrary radius $R$; Theorem 5.1 uses $R=D$. The lattice distance is `LatticeFamily.latticeDist`, and $\Delta(t_x,\mathcal C)$ is `codeDist`, cast to $\mathbb R$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma 5.2 (\label{lem:search-test}); Lean: LatticePrepro/Conversions/SearchTest.lean, LatticePrepro.CodeFamily.Accepts, LatticePrepro.CodeFamily.IsApprox, LatticePrepro.LatticeReduction.Accepts, LatticePrepro.LatticeReduction.IsApprox

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance

/-!
# Testing search outputs (Lemma 5.2)

For the code instances of Lemma 3.11 and the lattice instances of Lemma 3.12, a returned vector can
be tested: it is *accepted* if it lies in the code or lattice and its residual weight `w` is at
most `g · D`, where `w = dist(t_x, v)` for codes and `w` is the residual weight of the
`LatticeReduction` for lattices. Then

* on YES instances, every `f`-approximate solution is accepted (for `f < g` for codes and
  `16 · f^s ≤ g` for lattices);
* on NO instances, every vector is rejected.

The paper's computability claim (the test runs in polynomial time) is not formalized.
-/

namespace LatticePrepro

/-! ### Codes -/

namespace CodeFamily

variable {F : Type} [Field F] [DecidableEq F] {X : Type} (C : CodeFamily F X)

/-- The test of Lemma 5.2 for codes: a codeword is accepted if its Hamming distance from the
target is at most `g · R`. -/
def Accepts (g R : ℕ) (x : X) (c : C.M → F) : Prop :=
  c ∈ C.code ∧ hammingDist (C.target x) c ≤ g * R

/-- An `f`-approximate solution: a codeword within distance `f · dist(t_x, 𝒞)` of the target. -/
def IsApprox (f : ℝ) (x : X) (c : C.M → F) : Prop :=
  c ∈ C.code ∧ (hammingDist (C.target x) c : ℝ) ≤ f * codeDist (C.target x) C.code

end CodeFamily

/-! ### Lattices -/

namespace LatticeReduction

variable {p : ℕ} [Fact p.Prime] {X : Type} {L : LinearSystemFamily (ZMod p) X} {g : ℕ}
  {pn : PNorm} (Red : LatticeReduction L g pn)

/-- The test of Lemma 5.2 for lattices: a lattice vector is accepted if its residual weight is at
most `g · D`. -/
def Accepts (x : X) (v : Red.Λ.M → ℤ) : Prop :=
  v ∈ Red.Λ.lattice ∧ Red.weight x v ≤ g * L.numBlocks

/-- An `f`-approximate solution: a lattice vector within distance `f · dist_p(t_x, Λ)` of the
target. -/
def IsApprox (f : ℝ) (x : X) (v : Red.Λ.M → ℤ) : Prop :=
  v ∈ Red.Λ.lattice ∧ Red.Λ.dist pn x v ≤ f * Red.Λ.latticeDist pn x

end LatticeReduction

end LatticePrepro


