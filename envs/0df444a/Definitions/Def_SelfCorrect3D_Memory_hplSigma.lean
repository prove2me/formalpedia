-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_hplSigma
-- name    : SelfCorrect3D_Memory_hplSigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:48.876024+00:00
-- url     : https://prove2.me/theorems/8886f5d4-c898-4b98-aaa4-cfeb882271d2
-- title:
--   Geometric series $\Sigma=\sum_k(\delta h)^k\delta$ of the perturbation lemma
-- statement:
--   For linear maps $\delta,h$ on an $\mathbb F_2$-module $C$ and $N\in\mathbb N$, set
--
--   $$\Sigma=\sum_{k=0}^{N}(\delta h)^k\delta=\delta+\delta h\delta+\delta h\delta h\delta+\cdots .$$
--
--   When $(h\delta)^N=0$ (the smallness condition (33)) one has $(\delta h)^{N+1}=\delta(h\delta)^Nh=0$, so this finite sum is the whole series (246) of the homological perturbation lemma.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, Appendix A, eq. (246), p. 95; eq. (33), p. 15

import Mathlib

namespace SelfCorrect3D.Memory

/-- **The geometric-series sum `Σ = Σ_{k≥0} (δh)^k δ`** of the homological perturbation lemma,
Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, Appendix A, eq. (246), p. 95, truncated at `k = N`.

**Formalization Note.** Under the smallness condition `(hδ)^N = 0` (eq. (33), p. 15: "if there
exists a finite N for which (h d_pert)^N = 0") one has `(δh)^{N+1} = δ(hδ)^N h = 0`, so every term
with `k > N` vanishes and this finite sum is the whole series. Linear endomorphisms of an
`𝔽₂`-module; composition `∘ₗ`. -/
def hplSigma {C : Type} [AddCommGroup C] [Module (ZMod 2) C] (δ h : C →ₗ[ZMod 2] C) (N : ℕ) :
    C →ₗ[ZMod 2] C :=
  ∑ k ∈ Finset.range (N + 1), ((δ ∘ₗ h) ^ k) ∘ₗ δ

end SelfCorrect3D.Memory


