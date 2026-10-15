-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:06:30.863664+00:00
-- url     : https://prove2.me/theorems/46f39b66-2a37-45ac-bc90-19f91d31dfc4
-- title:
--   Conjugating a group representation by a bounded invertible operator
-- statement:
--   Let $G$ be a group, $H$ a complex Hilbert space and $\pi:G\to B(H)$ a homomorphism into the multiplicative monoid of bounded operators on $H$, so that each $\pi(g)$ is invertible with inverse $\pi(g^{-1})$; the file records $\pi(g)\bigl(\pi(g^{-1})x\bigr)=x$.
--
--   For a bounded linear bijection $S:H\to H$ with bounded inverse, the **conjugated representation** $\pi^S:G\to B(H)$ is
--   $$\pi^S(g)=S\,\pi(g)\,S^{-1},\qquad\text{i.e.}\qquad\pi^S(g)x=S\bigl(\pi(g)(S^{-1}x)\bigr)\quad(g\in G,\ x\in H).$$
--   It is again a homomorphism: $\pi^S(1)=\mathrm{id}$ and $\pi^S(gh)=\pi^S(g)\,\pi^S(h)$.
--
--   A representation $\pi$ is similar to a unitary one exactly when some such $S$ makes every $\pi^S(g)$ an isometry. The conjugated representation is the device behind the module's main result: if $\pi$ is similar to a unitary representation, then every closed $\pi$-invariant subspace $M$ admits a bounded projection $P$ with range in $M$, $Px=x$ for $x\in M$, commuting with every $\pi(g)$. For a triangular representation $\begin{pmatrix}U&DU\\0&U\end{pmatrix}$ on $H\oplus H$ the first summand is invariant, and writing such a projection as $\begin{pmatrix}1&X\\0&0\end{pmatrix}$, commutation with all $\pi(g)$ says exactly that $D(g)=B-U(g)BU(g^{-1})$ with $B=-X$.
--
--   **Formalization Note** $S$ is a continuous linear equivalence `H ≃L[ℂ] H`, $\pi^S$ is `conjugated π S` with evaluation lemma `conjugated_apply`, and the inverse identity is `rep_inv`. The file assumes $H$ complete, although these two lemmas do not use completeness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/InvariantProjection.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/InvariantProjection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DixmierAllDiscrete mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete

namespace OAI

/-! A unitarizing similarity gives a bounded commuting projection
onto every closed invariant subspace. -/
noncomputable section
namespace Dixmier
namespace InvariantProjection
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
@[simp] theorem rep_inv (U : G →* (H →L[ℂ] H)) (g : G) (x : H) : U g (U g⁻¹ x) = x := by
  have h : U g * U g⁻¹ = 1 := by rw [← map_mul]; simp
  exact congrArg (fun T : H →L[ℂ] H => T x) h

def conjugated (π : G →* (H →L[ℂ] H)) (S : H ≃L[ℂ] H) : G →* (H →L[ℂ] H) where
  toFun g := S.toContinuousLinearMap.comp ((π g).comp S.symm.toContinuousLinearMap)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [map_mul, mul_apply_eq_comp]

omit [CompleteSpace H] in
@[simp] theorem conjugated_apply (π : G →* (H →L[ℂ] H)) (S : H ≃L[ℂ] H) (g : G) (x : H) :
    conjugated π S g x = S (π g (S.symm x)) := rfl

end InvariantProjection
end Dixmier

end

end OAI


