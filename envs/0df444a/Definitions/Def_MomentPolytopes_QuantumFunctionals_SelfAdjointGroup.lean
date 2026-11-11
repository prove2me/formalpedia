-- Prove2me | Definitions.Def_MomentPolytopes_QuantumFunctionals_SelfAdjointGroup
-- name    : MomentPolytopes_QuantumFunctionals_SelfAdjointGroup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:02:28.30767+00:00
-- url     : https://prove2.me/theorems/1d26fd4a-8f71-4028-94ca-38d9c28f2918
-- title:
--   Connected Zariski-closed self-adjoint subgroups G ⊆ GL(n), with K = G ∩ U(n) and H = Lie G ∩ Herm(n)
-- statement:
--   A subgroup $G\subseteq\mathrm{GL}(n)$ is **Zariski-closed** if it is the set of invertible matrices on which some family of complex polynomials in the matrix entries vanishes; it is **self-adjoint** if $g^\dagger\in G$ for all $g\in G$. We consider **connected** such $G$, with
--   $$P=G\cap\mathrm{PD}(n),\qquad K=G\cap\mathrm U(n),\qquad H=\operatorname{Lie}G\cap\mathrm{Herm}(n)=\{X\in\mathrm{Herm}(n)\mid e^{tX}\in G\ \forall t\in\mathbb R\}.$$
--
--   **Formalization Note** Connectedness is taken in the Euclidean topology of matrices; for a complex algebraic group it is equivalent to Zariski-connectedness. Closed sets of $\mathrm{GL}(n)$ cut out by polynomials in the entries and $\det^{-1}$ are the same as those cut out by polynomials in the entries alone (multiply by a power of $\det$).
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), §2.3, p. 15; §6.1, p. 29

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace MomentPolytopes.QuantumFunctionals

/-- `G ⊆ GL(n)` is a **connected, Zariski-closed, self-adjoint subgroup** (§2.3, p. 15; §6.1,
p. 29): a subgroup of the invertible matrices, equal to the set of invertible matrices on which
some family of complex polynomials in the matrix entries vanishes, closed under `g ↦ g†`, and
connected (for a complex algebraic group, Zariski- and Euclidean-connectedness agree; the
Euclidean topology is used). -/
structure IsConnSelfAdjointAlgGroup {n : ℕ} (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop where
  one_mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ G
  mul_mem : ∀ g h, g ∈ G → h ∈ G → g * h ∈ G
  inv_mem : ∀ g, g ∈ G → g⁻¹ ∈ G
  zariskiClosed : ∃ S : Set (MvPolynomial (Fin n × Fin n) ℂ),
    G = {g | g.det ≠ 0 ∧ ∀ q ∈ S, MvPolynomial.eval (fun ij => g ij.1 ij.2) q = 0}
  selfAdjoint : ∀ g, g ∈ G → gᴴ ∈ G
  connected : IsConnected G

/-- `K = G ∩ U(n)`. -/
def groupK {n : ℕ} (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {u | u ∈ G ∧ u ∈ Matrix.unitaryGroup (Fin n) ℂ}

/-- `H = Lie G ∩ Herm(n)`: Hermitian `X` with `e^{tX} ∈ G` for all real `t`. -/
def groupH {n : ℕ} (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | X.IsHermitian ∧ ∀ t : ℝ, hermExp t X ∈ G}

end MomentPolytopes.QuantumFunctionals


