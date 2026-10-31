-- Prove2me | Definitions.Def_InfHorizonVP_polarDual
-- name    : InfHorizonVP_polarDual
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:10.420926+00:00
-- url     : https://prove2.me/theorems/0922ed6c-2fee-401d-bfcd-8f1cbcf1e93b
-- title:
--   Polar $C^0\subseteq E^*$ of a set $C\subseteq E$
-- statement:
--   For $C\subseteq E$, the **polar** is $C^0=\{x^*\in E^*\mid s(x^*,C)\le0\}=\{x^*\mid\langle x^*,x\rangle\le0\ \forall x\in C\}$. The polar mapping of a multifunction $\Gamma$ is $\Gamma^0(t)=\Gamma(t)^0$.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §2, p.4; §A.3, p.23

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Polar `C⁰` of a subset `C` of `E`, in `E*`.**
Frankowska, Sagara, arXiv:1801.00400v3, §2, p.4: "The support function s(·, C) : E* → R ∪ {+∞}
of a nonempty subset C of E is given by s(x*, C) = sup_{x∈C} ⟨x*, x⟩. The polar C⁰ of C is the set
C⁰ = {x* ∈ E* | s(x*, C) ≤ 0}." Used in Lemma A.1 (p.23): "Γ⁰ : I ⇝ E* the polar mapping of Γ
defined by Γ⁰(t) := Γ(t)⁰".

**Formalization Note.** `s(x*, C) ≤ 0` is written `∀ x ∈ C, x* x ≤ 0` (the same condition). -/
def polarDual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) : Set (E →L[ℝ] ℝ) :=
  {z | ∀ x ∈ C, z x ≤ 0}

end InfHorizonVP


