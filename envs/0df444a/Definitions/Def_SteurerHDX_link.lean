-- Prove2me | Definitions.Def_SteurerHDX_link
-- name    : SteurerHDX_link
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:45.908897+00:00
-- url     : https://prove2.me/theorems/99989726-bf29-40b7-b591-99353a61bdfd
-- title:
--   The link $\mathcal X_\tau$ of a face
-- statement:
--   For a face $\tau$ of a complex $\mathcal X$, the **link** of $\tau$ is the complex
--   $$\mathcal X_\tau=\{\sigma\setminus\tau : \sigma\in\mathcal X,\ \sigma\supseteq\tau\}.$$
--   Links are the local pieces whose expansion controls the global expansion of the complex.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.2, p.3

import Mathlib

namespace SteurerHDX

/-- **The link of a face.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.2, p.3: "For a face τ ∈ X, define the link of τ as
the simplicial complex X_τ = {σ \ τ | σ ∈ X, σ ⊇ τ}." -/
def link {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (τ : Finset V) :
    Finset (Finset V) :=
  (X.filter (fun σ => τ ⊆ σ)).image (fun σ => σ \ τ)

end SteurerHDX


