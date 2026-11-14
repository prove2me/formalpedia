-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_PottsWeighted
-- name    : ZeroFreeRRG_Hardcore_PottsWeighted
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T08:47:26.761232+00:00
-- url     : https://prove2.me/theorems/4910f72a-a406-4531-80ae-2b9d4748c8e8
-- title:
--   Edge-weighted Potts sums with fixed vertex colors
-- statement:
--   The weighted partition sum fixes colors on a vertex set and sums over all extensions, multiplying a symmetric color-pair interaction for each edge. It includes the ordinary restricted Potts sum as a special case and permits edge interactions to vary during the zero-free-region argument.
-- source:
--   Auxiliary definition for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Mathlib
open scoped Classical BigOperators
namespace ZeroFreeRRG.Hardcore

/-- A symmetric edge-specific interaction matrix, evaluated on an unordered edge. -/
noncomputable def pottsEdgeWeight {V : Type} {q : ℕ}
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (σ : V → Fin q) (e : Sym2 V) : ℂ :=
  Sym2.lift ⟨fun u v => W s(u,v) (σ u) (σ v), by
    intro u v
    change W s(u,v) (σ u) (σ v) = W s(v,u) (σ v) (σ u)
    rw [Sym2.eq_swap, hW]⟩ e

/-- A weighted Potts sum restricted to prescribed colors on a finite vertex set. -/
noncomputable def pottsWeightedPartial {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (S : Finset V) (τ : V → Fin q) : ℂ :=
  ∑ σ : V → Fin q, if ∀ v ∈ S, σ v = τ v then
    ∏ e ∈ G.edgeFinset, pottsEdgeWeight W hW σ e else 0

end ZeroFreeRRG.Hardcore


