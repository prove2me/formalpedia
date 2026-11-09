-- Prove2me | Definitions.Def_DetPermanentApprox_Main_Analysis
-- name    : DetPermanentApprox_Main_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:34.688204+00:00
-- url     : https://prove2.me/theorems/97e7747e-1dc4-4daa-ade2-2fede023dd77
-- title:
--   Finite path trees and the normalized holomorphic logarithm
-- statement:
--   For an induced vertex set and a root, path-tree vertices are injective vertex sequences starting at the root, with successive vertices joined by an edge and every vertex in the induced set. Their lengths range from one through the ambient vertex count. The root is the length-one sequence. The symmetric matrix assigns $\sqrt{w_e}$ to a one-edge extension by $e$ and zero otherwise. The Euclidean norm bound is expressed by its action on every real vector.
--
--   The transformed partition function is $Z_G(\tau(z)e^y)$, where $\tau(z)=\rho z/(1-z)$. Its normalized logarithm is defined by the integral of the logarithmic derivative along the radial segment from zero to $z$. On a zero-free disk it is the holomorphic logarithm vanishing at zero; no logarithm property is asserted on degenerate inputs. These definitions support both resolvent and log-weight derivative statements.
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), §§3.2–3.3, pp. 14–18 (PDF pp. 14–18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Surrogate

open scoped BigOperators

namespace DetPermanentApprox.Main

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

abbrev RawPath (V : Type) [Fintype V] :=
  Σ l : Fin (Fintype.card V + 1), Fin l.val → V

def PathCondition (G : Graph V E) (S : Finset V) (v : V) (p : RawPath V) : Prop :=
  (∃ h : 0 < p.1.val, p.2 ⟨0, h⟩ = v) ∧ Function.Injective p.2 ∧
    (∀ i, p.2 i ∈ S) ∧
    (∀ i j, j.val = i.val + 1 → ∃ e, G.ends e = s(p.2 i, p.2 j))

abbrev Path (G : Graph V E) (S : Finset V) (v : V) :=
  {p : RawPath V // PathCondition G S v p}

noncomputable instance pathFintype (G : Graph V E) (S : Finset V) (v : V) :
    Fintype (Path G S v) := Fintype.ofFinite _

def rootPath (G : Graph V E) (S : Finset V) (v : V) (hv : v ∈ S) : Path G S v := by
  have hc : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  refine ⟨⟨⟨1, by omega⟩, fun _ => v⟩, ?_⟩
  refine ⟨⟨by change 0 < (1 : ℕ); omega, rfl⟩, ?_, ?_, ?_⟩
  · intro i j h
    exact Subsingleton.elim i j
  · intro i
    exact hv
  · intro i j h
    have hi := i.isLt
    have hj := j.isLt
    change i.val < 1 at hi
    change j.val < 1 at hj
    change j.val = i.val + 1 at h
    omega

def ExtendsBy (G : Graph V E) {S : Finset V} {v : V}
    (p q : Path G S v) (e : E) : Prop :=
  q.val.1.val = p.val.1.val + 1 ∧
    (∀ i j, i.val = j.val → p.val.2 i = q.val.2 j) ∧
    (∃ i j, i.val + 1 = p.val.1.val ∧ j.val + 1 = q.val.1.val ∧
      G.ends e = s(p.val.2 i, q.val.2 j))

open Classical in
noncomputable def pathMatrix (G : Graph V E) (S : Finset V) (v : V) (w : E → ℝ) :
    Matrix (Path G S v) (Path G S v) ℝ :=
  fun p q => ∑ e, if ExtendsBy G p q e ∨ ExtendsBy G q p e then Real.sqrt (w e) else 0

noncomputable def squaredNorm {I : Type} [Fintype I] (x : I → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- Euclidean operator-norm upper bound, expressed without changing the default
supremum norm on Lean's finite function type. -/
def EuclideanBound {I : Type} [Fintype I] (B : Matrix I I ℝ) (c : ℝ) : Prop :=
  ∀ x : I → ℝ, Real.sqrt (squaredNorm (B.mulVec x)) ≤ c * Real.sqrt (squaredNorm x)

noncomputable def transformedPartition (G : Graph V E) (K : ℚ) (y : E → ℝ) (z : ℂ) : ℂ :=
  complexZ G Finset.univ (fun e => tau K z * (Real.exp (y e) : ℂ))

/-- Normalized logarithm obtained by integrating the logarithmic derivative along
the radial segment. On a zero-free disk it is the unique holomorphic log vanishing
at zero. Away from that domain no logarithm claim is made about this total term. -/
noncomputable def normalizedLog (G : Graph V E) (K : ℚ) (y : E → ℝ) (z : ℂ) : ℂ :=
  ∫ r in (0 : ℝ)..1,
    z * deriv (transformedPartition G K y) ((r : ℂ) * z) /
      transformedPartition G K y ((r : ℂ) * z)

end DetPermanentApprox.Main


