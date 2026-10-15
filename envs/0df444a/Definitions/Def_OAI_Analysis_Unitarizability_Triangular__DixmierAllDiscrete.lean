-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:05:02.579742+00:00
-- url     : https://prove2.me/theorems/d5c38a4d-64f0-43a4-9b82-752aed3c522e
-- title:
--   Upper-triangular representations on $H\oplus H$ built from a representation and a cocycle
-- statement:
--   Let $G$ be a group and $H$ a complex inner product space, and write $B(H)$ for the bounded linear operators on $H$.
--
--   1. **The Hilbert double.** $H\oplus_2H$ is $H\times H$ with the norm $\|(x,y)\|=\bigl(\|x\|^2+\|y\|^2\bigr)^{1/2}$. The coordinate embeddings $\iota_1x=(x,0)$ and $\iota_2y=(0,y)$ are bounded linear isometries $H\to H\oplus_2H$.
--   2. **Diagonal operators.** For $U\in B(H)$, $\operatorname{diag}(U)(x,y)=(Ux,\,Uy)$.
--   3. **Triangular operators.** For $U,D\in B(H)$,
--   $$\Theta(U,D)(x,y)=\bigl(Ux+DUy,\ Uy\bigr),\qquad\text{that is,}\qquad\Theta(U,D)=\begin{pmatrix}U&DU\\0&U\end{pmatrix}.$$
--   4. **Triangular representation.** Let $U:G\to B(H)$ be a homomorphism into the multiplicative monoid of $B(H)$, so $U(1)=\mathrm{id}$ and $U(gh)=U(g)U(h)$ (the file records $U(g^{-1})U(g)x=x$), and let $D:G\to B(H)$ satisfy $D(1)=0$ and the twisted cocycle identity
--   $$D(gh)=D(g)+U(g)\,D(h)\,U(g^{-1})\qquad(g,h\in G).$$
--   Then $\pi_{U,D}(g)=\Theta\bigl(U(g),D(g)\bigr)$ defines a group homomorphism $\pi_{U,D}:G\to B(H\oplus_2H)$.
--
--   Triangular representations are how representations that are not similar to unitary ones are produced. Every coboundary $D(g)=B-U(g)BU(g^{-1})$ with $B\in B(H)$ satisfies the cocycle identity; conversely, a separate result of the development shows for complete $H$ that if $\pi_{U,D}$ is similar to a unitary representation, then $D$ is such a coboundary. If every $U(g)$ is an isometry and $\|D(g)\|\le\kappa$ for all $g$, then $\|\pi_{U,D}(g)\|\le1+\kappa$, so a bounded cocycle that is not a bounded coboundary gives a uniformly bounded representation that is not unitarizable.
--
--   **Formalization Note** $H\oplus_2H$ is `Double H`, an abbreviation for `WithLp 2 (H × H)`; the embeddings are `inl` and `inr`, the operators are `diagonal U` and `operator U D`, and the representation is `representation U D h1 hD`, with the cocycle identity written via `conjugate U g`. The simp lemmas `inl_apply`, `inr_apply`, `inl_norm`, `inr_norm`, `diagonal_fst`, `diagonal_snd`, `operator_fst`, `operator_snd` and `inv_apply` record the formulas above. Completeness of $H$ is not assumed here. The hypothesis $D(1)=0$ also follows from the cocycle identity at $g=h=1$, but it is passed explicitly.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Triangular.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Triangular.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DixmierAllDiscrete mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete

namespace OAI

/-! Bounded Hilbert sums and triangular representations. -/
noncomputable section
namespace Dixmier
namespace Triangular
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
abbrev Double (H : Type*) := WithLp 2 (H × H)

def inl : H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H H)

def inr : H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ H H)

@[simp] theorem inl_apply (x : H) : inl x = WithLp.toLp 2 (x,0) := rfl
@[simp] theorem inr_apply (x : H) : inr x = WithLp.toLp 2 (0,x) := rfl
@[simp] theorem inl_norm (x : H) : ‖inl x‖ = ‖x‖ := WithLp.norm_toLp_fst 2 H H x
@[simp] theorem inr_norm (x : H) : ‖inr x‖ = ‖x‖ := WithLp.norm_toLp_snd 2 H H x

def diagonal (U : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  inl.comp (U.comp (WithLp.fstL 2 ℂ H H)) +
    inr.comp (U.comp (WithLp.sndL 2 ℂ H H))

@[simp] theorem diagonal_fst (U : H →L[ℂ] H) (x : Double H) :
    (diagonal U x).fst = U x.fst := by simp [diagonal, inl, inr]
@[simp] theorem diagonal_snd (U : H →L[ℂ] H) (x : Double H) :
    (diagonal U x).snd = U x.snd := by simp [diagonal, inl, inr]

def operator (U D : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  diagonal U + inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H)))

@[simp] theorem operator_fst (U D : H →L[ℂ] H) (x : Double H) :
    (operator U D x).fst = U x.fst + D (U x.snd) := by simp [operator, inl]
@[simp] theorem operator_snd (U D : H →L[ℂ] H) (x : Double H) :
    (operator U D x).snd = U x.snd := by simp [operator, inl]

@[simp] theorem inv_apply (U : G →* (H →L[ℂ] H)) (g : G) (x : H) : U g⁻¹ (U g x) = x := by
  have h : U g⁻¹ * U g = 1 := by rw [← map_mul]; simp
  exact congrArg (fun T : H →L[ℂ] H => T x) h

def representation (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h)) :
    G →* (Double H →L[ℂ] Double H) where
  toFun g := operator (U g) (D g)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext <;> simp [h1]
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext
    · change (operator (U (g*h)) (D (g*h)) x).fst =
        (operator (U g) (D g) (operator (U h) (D h) x)).fst
      simp only [operator_fst, operator_snd, map_mul, hD, conjugate,
        add_apply, mul_apply_eq_comp, map_add, inv_apply]
      abel
    · simp [map_mul, mul_apply_eq_comp]

end Triangular
end Dixmier

end

end OAI


