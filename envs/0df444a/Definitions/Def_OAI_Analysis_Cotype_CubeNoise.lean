-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_CubeNoise
-- name    : OAI_Analysis_Cotype_CubeNoise
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:34:16.095062+00:00
-- url     : https://prove2.me/theorems/e7e2d587-d354-4fba-8546-11810ba85156
-- title:
--   The noise operator with correlation one half
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $f:\{0,1\}^n\to X$.
--
--   1. **Splitting the first coordinate.** $\{0,1\}\times\{0,1\}^n\cong\{0,1\}^{n+1}$ by prepending a bit.
--   2. **Noise.** $N_0f=f$, and recursively
--   $$
--   (Nf)(b,u)=\tfrac34(Nf_b)(u)+\tfrac14(Nf_{\bar b})(u),
--   $$
--   where $f_b$ fixes the first bit. Each bit is kept with probability $\frac34$ and flipped with probability $\frac14$, so $N=T_{1/2}$ multiplies $w_A$ by $2^{-|A|}$. It is a positive averaging operator, so $\|Nf(u)\|\le N(\|f\|)(u)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/CubeNoise.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/CubeNoise.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def cubeCons (n : ℕ) : Bool × Cube n ≃ Cube (n+1) where
  toFun p := Fin.cons p.1 p.2
  invFun u := (u 0, Fin.tail u)
  left_inv p := by ext i <;> simp
  right_inv u := by ext i; exact Fin.cases (by simp) (fun i => by simp; rfl) i

def cubeNoise : {n : ℕ} → (Cube n → X) → Cube n → X
  | 0, f, u => f u
  | _+1, f, u =>
    if u 0 then
      (1/4 : ℝ) • cubeNoise (fun v => f (Fin.cons false v)) (Fin.tail u) +
      (3/4 : ℝ) • cubeNoise (fun v => f (Fin.cons true v)) (Fin.tail u)
    else
      (3/4 : ℝ) • cubeNoise (fun v => f (Fin.cons false v)) (Fin.tail u) +
      (1/4 : ℝ) • cubeNoise (fun v => f (Fin.cons true v)) (Fin.tail u)

@[simp] theorem cubeNoise_cons_false {n : ℕ} (f : Cube (n+1) → X) (u : Cube n) :
    cubeNoise f (Fin.cons false u) =
      (3/4 : ℝ) • cubeNoise (fun v => f (Fin.cons false v)) u +
      (1/4 : ℝ) • cubeNoise (fun v => f (Fin.cons true v)) u := by simp [cubeNoise]

@[simp] theorem cubeNoise_cons_true {n : ℕ} (f : Cube (n+1) → X) (u : Cube n) :
    cubeNoise f (Fin.cons true u) =
      (1/4 : ℝ) • cubeNoise (fun v => f (Fin.cons false v)) u +
      (3/4 : ℝ) • cubeNoise (fun v => f (Fin.cons true v)) u := by simp [cubeNoise]

end Cotype

end

end OAI


