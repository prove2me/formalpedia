-- Prove2me | Definitions.Def_GaussDiffSVP_IsCoinKernel
-- name    : GaussDiffSVP_IsCoinKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:49.745698+00:00
-- url     : https://prove2.me/theorems/57dde40e-0870-4f94-985d-37918b73b3ac
-- title:
--   Pairwise independent activation coins with marginals $q$
-- statement:
--   Given two completed child lists, a **coin kernel** is a law on the activation pattern $(B_{ij})$ of all ordered pairs of child records. It has marginals $q$ and pairwise independent coins if
--   $$\Pr[B_{ij}=1] = q(X_i,Y_j),\qquad \Pr[B_{ij}=1,\ B_{i'j'}=1] = q(X_i,Y_j)\,q(X_{i'},Y_{j'})\quad\text{for }(i,j)\ne(i',j').$$
--   This is the paper's activation law: "Distinct pair coins are conditionally pairwise independent given the completed child lists." No mutual independence is assumed.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §4.1, p.22

import Mathlib

open scoped ENNReal

namespace GaussDiffSVP

/-- The activation law of a merge (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §4.1, p.22): "For each ordered pair of child IDs `(i, j)`,
let `B_{ij} ∈ {0, 1}` indicate whether the pair is activated … with
`E[B_{ij} | Ξ_L, Ξ_R] = q(X_i, Y_j) ∈ [0, 1]`. … Distinct pair coins are conditionally pairwise
independent given the completed child lists." A coin kernel `κ` gives, for every pair of completed
child lists, a law on the activation pattern `B : Fin |l_L| × Fin |l_R| → Bool`; it has marginals
`q` and pairwise independent coins when every pair `(i, j)` is activated with probability
`q(X_i, Y_j)` and every two distinct pairs are both activated with probability
`q(X_i, Y_j) q(X_{i′}, Y_{j′})`.

**Formalization Note.** For `{0,1}`-valued coins, pairwise independence is exactly this product
rule. No mutual independence is assumed. Such a kernel can exist only if `q ≤ 1`. -/
def IsCoinKernel {α β : Type*} (q : α → β → ℝ≥0∞)
    (κ : (lL : List α) → (lR : List β) → PMF (Fin lL.length × Fin lR.length → Bool)) : Prop :=
  ∀ (lL : List α) (lR : List β),
    (∀ e : Fin lL.length × Fin lR.length,
      (κ lL lR).toOuterMeasure {B | B e = true} = q (lL.get e.1) (lR.get e.2)) ∧
    ∀ e e' : Fin lL.length × Fin lR.length, e ≠ e' →
      (κ lL lR).toOuterMeasure {B | B e = true ∧ B e' = true} =
        q (lL.get e.1) (lR.get e.2) * q (lL.get e'.1) (lR.get e'.2)

end GaussDiffSVP


