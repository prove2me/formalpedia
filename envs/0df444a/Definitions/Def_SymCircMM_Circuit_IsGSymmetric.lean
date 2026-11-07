-- Prove2me | Definitions.Def_SymCircMM_Circuit_IsGSymmetric
-- name    : SymCircMM_Circuit_IsGSymmetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:31:23.111023+00:00
-- url     : https://prove2.me/theorems/4a555bc2-0f7e-426e-965a-7d39ddcc35f2
-- title:
--   Circuits computing $\mathrm{MM}_n$, and $G$-symmetry for $G\le S_n$ acting by (2)
-- statement:
--   Let $G\le S_n$ act on the variables of matrix multiplication by (2).
--
--   1. A circuit **computes $\mathrm{MM}_n$** if there are gates $\mathrm{out}(a,b)$, $a,b\in[n]$, with $\widehat{\mathrm{out}(a,b)}=(AB)_{ab}$ as polynomials; all entries are computed simultaneously.
--   2. A circuit is **$G$-symmetric** if for every $\sigma\in G$ there is a bijection of its gates that preserves every edge multiplicity and every gate label, input variables being renamed by $\sigma$ as in (2).
--   3. A circuit is **$G$-symmetric with output gates $\mathrm{out}$ in the sense of Definition 2.2** if each variable and each constant labels at most one input gate and every $\sigma\in G$ extends, as in 2, to an automorphism $\hat\sigma$ fixing every output gate, $\hat\sigma\cdot g_r=g_r$ (the requirement of Remark 2.4 for the individually invariant entries of $\mathrm{MM}_n$).
--
--   The same notions are defined for weighted circuits, whose automorphisms also preserve the edge scalars.
--
--   These are the hypotheses of the lower bounds (notion 2) and the shape of the circuits whose existence is asserted (notion 3).
--
--   **Formalization Note** Notion 2 (`IsGSymmetric`) is the relaxed version used in every lower bound: input labels may repeat and nothing is required of the output gates, so it covers every circuit symmetric in the paper's sense. Notion 3 (`IsGSymmetricStrict`) is the paper's notion and is used in every existence clause. Equality of computed values is equality in `MvPolynomial`, not of polynomial functions.
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Definition 2.2, p.3 (PDF p.4); Remark 2.4 and Definition 2.5, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_SymCircMM_WCircuit
import Definitions.Def_SymCircMM_MMVar

set_option autoImplicit false

namespace SymCircMM

variable {F ι γ : Type} [Field F]

/-- The gates `out (a, b)` compute the entries of `MM_n`: `out (a, b)` computes the polynomial
`(AB)_{ab} = ∑_j A_{aj} B_{jb}` (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix
Multiplication*, manuscript (sha256 999a7eba…), §2.3, p.5 (PDF p.6); equality of polynomials, not of
polynomial functions). -/
def Circuit.ComputesMMAt [Fintype ι] [Fintype γ] (C : Circuit F (MMVar ι) γ) (out : ι × ι → γ) :
    Prop :=
  ∀ a b, C.val (out (a, b)) = mmEntry F a b

/-- The circuit **computes `MM_n`**: some gates compute all the entries `(AB)_{ab}` simultaneously
(Definition 2.5, p.4 (PDF p.5)). -/
def Circuit.ComputesMM [Fintype ι] [Fintype γ] (C : Circuit F (MMVar ι) γ) : Prop :=
  ∃ out : ι × ι → γ, C.ComputesMMAt out

/-- A circuit for matrix multiplication is **`G`-symmetric** for a group `G ≤ S_n` acting by (2)
(Definition 2.2, p.3 (PDF p.4)): for every `σ ∈ G` the map `g_x ↦ g_{σ·x}`, `g_c ↦ g_c` on input gates
extends to an automorphism of the circuit as a labelled multi-DAG.

**Formalization Note.** The extension is any wire- and label-compatible bijection `φ` of the gates
(`Circuit.Extends`). No condition is put on output gates (Definition 2.2 derives "σ̂ permutes the output
gates" as a consequence), and several input gates may carry the same variable. -/
def Circuit.IsGSymmetric (G : Subgroup (Equiv.Perm ι)) (C : Circuit F (MMVar ι) γ) : Prop :=
  ∀ σ ∈ G, ∃ φ : γ ≃ γ, C.Extends (mmAct σ) φ

/-- Every input label (variable or constant) is carried by at most one input gate, as Definition 2.2
presupposes when it speaks of "the" input gate `g_x` (p.3 (PDF p.4)). -/
def Circuit.InputsDistinct (C : Circuit F (MMVar ι) γ) : Prop :=
  ∀ g g', (C.label g).isLeaf = true → C.label g = C.label g' → g = g'

/-- **`G`-symmetric with the output gates `out`, in the sense of Definition 2.2 and Remark 2.4**
(pp.3–4 (PDF pp.4–5)): each variable and each constant labels at most one input gate, and for every
`σ ∈ G` the map `g_x ↦ g_{σ·x}`, `g_c ↦ g_c` extends to an automorphism `σ̂` of the circuit that fixes
every output gate (`σ̂ · g_r = g_r`, the requirement of Remark 2.4 for the individually invariant
entries of `MM_n`). This is the paper's notion; `Circuit.IsGSymmetric` drops the two extra clauses. -/
def Circuit.IsGSymmetricStrict (G : Subgroup (Equiv.Perm ι)) (C : Circuit F (MMVar ι) γ)
    (out : ι × ι → γ) : Prop :=
  C.InputsDistinct ∧ ∀ σ ∈ G, ∃ φ : γ ≃ γ, C.Extends (mmAct σ) φ ∧ ∀ p, φ (out p) = out p

/-- The gates `out (a, b)` of a weighted circuit compute the entries `(AB)_{ab}` as polynomials. -/
def WCircuit.ComputesMMAt [Fintype ι] [Fintype γ] (C : WCircuit F (MMVar ι) γ)
    (out : ι × ι → γ) : Prop :=
  ∀ a b, C.val (out (a, b)) = mmEntry F a b

/-- A weighted circuit for matrix multiplication is `G`-symmetric: every `σ ∈ G` acting by (2)
extends to an automorphism preserving edges, labels and edge scalars. -/
def WCircuit.IsGSymmetric (G : Subgroup (Equiv.Perm ι)) (C : WCircuit F (MMVar ι) γ) : Prop :=
  ∀ σ ∈ G, ∃ φ : γ ≃ γ, C.Extends (mmAct σ) φ

/-- A weighted circuit is `G`-symmetric with the output gates `out` in the sense of Definition 2.2 and
Remark 2.4: one input gate per label, and every `σ ∈ G` extends to an automorphism (preserving the
edge scalars) fixing every output gate. -/
def WCircuit.IsGSymmetricStrict (G : Subgroup (Equiv.Perm ι)) (C : WCircuit F (MMVar ι) γ)
    (out : ι × ι → γ) : Prop :=
  C.toCircuit.InputsDistinct ∧ ∀ σ ∈ G, ∃ φ : γ ≃ γ, C.Extends (mmAct σ) φ ∧ ∀ p, φ (out p) = out p

end SymCircMM


