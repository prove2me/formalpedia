-- Prove2me | Definitions.Def_DeMorganApprox_Main_GateComposition
-- name    : DeMorganApprox_Main_GateComposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:51.297288+00:00
-- url     : https://prove2.me/theorems/5d8056ed-e687-4cc0-a4d1-fb35d56a9512
-- title:
--   Lemma 5.3 construction — OR and AND composition of two span programs
-- statement:
--   Let $P_1,P_2$ be span programs with targets $u_1,u_2$ on orthogonal ambient spaces $H_1,H_2$, with witness parameters $(A_1,B_1)$ and $(A_2,B_2)$. The parent program lives on $H_1\oplus^\perp H_2$, keeps all listed vectors of both children with their labels, and has target
--   $$u=\cos\theta\,u_1+\sin\theta\,u_2 .$$
--   At an **OR** gate, $\cos^2\theta=\frac{A_1+1}{A_1+A_2+2}$, $\sin^2\theta=\frac{A_2+1}{A_1+A_2+2}$, one always-available **rotation vector** $r=\sin\theta\,u_1-\cos\theta\,u_2$ is added, and the parent parameters are
--   $$A=A_1+A_2+1,\qquad B=\cos^2\theta\,B_1+\sin^2\theta\,B_2 .$$
--   At an **AND** gate, $\cos^2\theta=\frac{B_1}{B_1+B_2}$, $\sin^2\theta=\frac{B_2}{B_1+B_2}$, no vector is added, and
--   $$A=\cos^2\theta\,A_1+\sin^2\theta\,A_2,\qquad B=B_1+B_2 .$$
--   $\cos\theta$ and $\sin\theta$ are the nonnegative square roots of these fractions.
--
--   This is the local step of the construction of §5; the heavy-chain program applies the same angles and parameters along each chain.
--
--   **Formalization Note** The orthogonal direct sum is the coordinate type $\iota_1\oplus\iota_2$, child vectors being extended by zero. The OR program's columns are $(J_1\oplus J_2)\oplus\mathrm{Unit}$, the extra column being $r$; the AND program's columns are $J_1\oplus J_2$.
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Lemma 5.3 and its proof, PDF pp. 17–19 (printed pp. 15–17), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf

import Mathlib
import Definitions.Def_DeMorganApprox_Main_SpanPrograms

namespace DeMorganApprox.Main

/-- OR angle (Lemma 5.3 proof, PDF p. 18): `cos²θ = (A₁+1)/(A₁+A₂+2)`, `sin²θ = (A₂+1)/(A₁+A₂+2)`;
returns `(cos θ, sin θ)` as nonnegative square roots. -/
noncomputable def orAngle (A₁ A₂ : ℝ) : ℝ × ℝ :=
  (Real.sqrt ((A₁ + 1) / (A₁ + A₂ + 2)), Real.sqrt ((A₂ + 1) / (A₁ + A₂ + 2)))

/-- AND angle (Lemma 5.3 proof, PDF p. 19): `cos²θ = B₁/(B₁+B₂)`, `sin²θ = B₂/(B₁+B₂)`. -/
noncomputable def andAngle (B₁ B₂ : ℝ) : ℝ × ℝ :=
  (Real.sqrt (B₁ / (B₁ + B₂)), Real.sqrt (B₂ / (B₁ + B₂)))

/-- Parent parameters at an OR gate: `A = A₁ + A₂ + 1`, `B = cos²θ B₁ + sin²θ B₂`. -/
noncomputable def orParams (A₁ B₁ A₂ B₂ : ℝ) : ℝ × ℝ :=
  (A₁ + A₂ + 1, (A₁ + 1) / (A₁ + A₂ + 2) * B₁ + (A₂ + 1) / (A₁ + A₂ + 2) * B₂)

/-- Parent parameters at an AND gate: `A = cos²θ A₁ + sin²θ A₂`, `B = B₁ + B₂`. -/
noncomputable def andParams (A₁ B₁ A₂ B₂ : ℝ) : ℝ × ℝ :=
  (B₁ / (B₁ + B₂) * A₁ + B₂ / (B₁ + B₂) * A₂, B₁ + B₂)

/-- The gate angle `(cos θ, sin θ)` for an OR (`isOr = true`) or AND gate. -/
noncomputable def gateAngle (isOr : Bool) (A₁ B₁ A₂ B₂ : ℝ) : ℝ × ℝ :=
  if isOr then orAngle A₁ A₂ else andAngle B₁ B₂

/-- The parent parameters for an OR (`isOr = true`) or AND gate. -/
noncomputable def gateParams (isOr : Bool) (A₁ B₁ A₂ B₂ : ℝ) : ℝ × ℝ :=
  if isOr then orParams A₁ B₁ A₂ B₂ else andParams A₁ B₁ A₂ B₂

namespace SpanProgram

variable {m : ℕ} {ι₁ ι₂ J₁ J₂ : Type}

/-- Lemma 5.3, OR case: ambient `ι₁ ⊕ ι₂` (orthogonal ambient spaces), target
`u = cos θ u₁ + sin θ u₂`, the columns of both children unchanged, plus one always-available
rotation vector `r = sin θ u₁ − cos θ u₂` (the `Sum.inr ()` column). -/
noncomputable def orCompose (P₁ : SpanProgram m ι₁ J₁) (P₂ : SpanProgram m ι₂ J₂) (A₁ A₂ : ℝ) :
    SpanProgram m (ι₁ ⊕ ι₂) ((J₁ ⊕ J₂) ⊕ Unit) where
  target := Sum.elim ((orAngle A₁ A₂).1 • P₁.target) ((orAngle A₁ A₂).2 • P₂.target)
  vec := Sum.elim
    (Sum.elim (fun j => Sum.elim (P₁.vec j) 0) (fun j => Sum.elim 0 (P₂.vec j)))
    (fun _ => Sum.elim ((orAngle A₁ A₂).2 • P₁.target) (-((orAngle A₁ A₂).1 • P₂.target)))
  label := Sum.elim (Sum.elim P₁.label P₂.label) (fun _ => Label.always)

/-- Lemma 5.3, AND case: ambient `ι₁ ⊕ ι₂`, target `u = cos θ u₁ + sin θ u₂`, the columns of
both children unchanged and no new column. -/
noncomputable def andCompose (P₁ : SpanProgram m ι₁ J₁) (P₂ : SpanProgram m ι₂ J₂) (B₁ B₂ : ℝ) :
    SpanProgram m (ι₁ ⊕ ι₂) (J₁ ⊕ J₂) where
  target := Sum.elim ((andAngle B₁ B₂).1 • P₁.target) ((andAngle B₁ B₂).2 • P₂.target)
  vec := Sum.elim (fun j => Sum.elim (P₁.vec j) 0) (fun j => Sum.elim 0 (P₂.vec j))
  label := Sum.elim P₁.label P₂.label

end SpanProgram

end DeMorganApprox.Main


