-- Prove2me | Definitions.Def_LowAccLTC_edgeTanner
-- name    : LowAccLTC_edgeTanner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:38:45.710228+00:00
-- url     : https://prove2.me/theorems/325f9dbc-d88c-422b-930f-f3030738c985
-- title:
--   Tanner codes from edge codes and their induced link codes
-- statement:
--   Let $Y$ be a weighted partite complex with local codes $C_{uv}\subseteq\Sigma^{\mathrm{star}(uv)}$ on the stars of its edges $uv\in Y\langle 2\rangle$. The global Tanner code is
--   $$C=\mathrm{Tan}(Y,\{C_{uv}\})=\{f:\ f|_{\mathrm{star}(uv)}\in C_{uv}\ \text{for every edge } uv\},$$
--   and for a vertex $v$ the induced code on the link is $C_v=\mathrm{Tan}(Y_v,\{C_{uv}\}_{u})$, the words on $\mathrm{star}(v)$ whose restriction to every $\mathrm{star}(uv)$ lies in $C_{uv}$. The local code of the link vertex $u$ of $Y_v$ is $C_{uv}$.
--
--   These are the codes of Proposition 5.11.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Proposition 5.11 p.48 (PDF p.51), §7 p.63 (PDF p.66)

import Definitions.Def_LowAccLTC_TannerCode

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

namespace PartiteComplex

variable {r : ℕ} {V T A : Type*} [Fintype T] (X : PartiteComplex r V T)

/-- The Tanner code `C = Tan(Y, {C_uv}_{uv ∈ Y⟨2⟩})` defined by local codes `C_uv ⊆ A^{star(uv)}`
on the stars of the edges of `Y` (Proposition 5.11, p.48, and §7, p.63): the words whose
restriction to `star(e)` lies in `C_e` for every edge `e`. -/
def edgeTanner (Ce : (e : Finset V) → Set (X.star e → A)) : Set (T → A) :=
  {f | ∀ e, X.IsFace e → e.card = 2 → (fun x : X.star e => f x.1) ∈ Ce e}

/-- The induced local Tanner code `C_v = Tan(Y_v, {C_uv}_{u ∈ Y_v⟨1⟩})` on the link of the
vertex `v` (Proposition 5.11, p.48): the words on `star(v)` whose restriction to `star(uv)` lies
in `C_uv` for every neighbour `u` of `v`. -/
def edgeLinkCode (Ce : (e : Finset V) → Set (X.star e → A)) (v : V) : Set (T → A) := by
  classical exact {h | ∀ u, u ≠ v → X.IsFace {u, v} → (fun x : X.star {u, v} => h x.1) ∈ Ce {u, v}}

/-- The local code at the link vertex `u` of the link `Y_v`: the edge code `C_uv`, as a set of
words read on `star(uv)`. -/
def edgeCodeAt (Ce : (e : Finset V) → Set (X.star e → A)) (v u : V) : Set (T → A) := by
  classical exact liftCode (X.star {u, v}) (Ce {u, v})

end PartiteComplex

end LowAccLTC


