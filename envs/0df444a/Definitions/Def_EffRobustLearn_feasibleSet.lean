-- Prove2me | Definitions.Def_EffRobustLearn_feasibleSet
-- name    : EffRobustLearn_feasibleSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:34:15.455521+00:00
-- url     : https://prove2.me/theorems/89c9aed5-a274-4756-887e-5ce39b81b7a0
-- title:
--   Sample vectors $f[S]$ and the feasible set $K$ (3.5)
-- statement:
--   For $f:X\to\mathbb R$, the vector of its values on the sample is $f[S]=((f(x))_{(x,y)\in\bar S_{\mathrm{inp}}},(f(x))_{x\in S_{\mathrm{ref}}})\in\mathbb R^{|\bar S_{\mathrm{inp}}|+|S_{\mathrm{ref}}|}$, with the Euclidean inner product. The feasible set of the online optimization is
--   $$K=\mathrm{conv}\{c[S]:c\in C\}.$$
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), p.12 (PDF p.13) and eq. (3.5), p.15 (PDF p.16)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM

namespace EffRobustLearn

/-- The Euclidean space `R^{|S̄inp| + |Sref|}` of vectors on the sample, Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.12. -/
abbrev SampleVec (n m : ℕ) : Type := EuclideanSpace ℝ (Fin n ⊕ Fin m)

/-- The vector `f[S] = ((f(x))_{(x,y)∈S̄inp}, (f(x))_{x∈Sref})`, p.12. -/
noncomputable def evalVec {X : Type*} {n m : ℕ} (f : X → ℝ) (Sinp : Fin n → X × Bool)
    (Sref : Fin m → X) : SampleVec n m :=
  WithLp.toLp 2 (Sum.elim (fun i => f (Sinp i).1) fun j => f (Sref j))

/-- The feasible set (3.5), p.15: `K = conv{c[S] : c ∈ C}`. -/
noncomputable def feasibleSet {X : Type*} {n m : ℕ} (C : Set (X → Bool)) (Sinp : Fin n → X × Bool)
    (Sref : Fin m → X) : Set (SampleVec n m) :=
  convexHull ℝ ((fun c => evalVec (toPM c) Sinp Sref) '' C)

end EffRobustLearn


