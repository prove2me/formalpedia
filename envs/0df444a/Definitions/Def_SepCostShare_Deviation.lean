-- Prove2me | Definitions.Def_SepCostShare_Deviation
-- name    : SepCostShare_Deviation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:24:44.528236+00:00
-- url     : https://prove2.me/theorems/3bef6de0-ea4c-45f1-8fb7-a085b21b7c48
-- title:
--   Cheapest alternative $\Delta^e_i(B)$, virtual cost value $\pi^e_i$, virtual deviation cost $\bar\Delta^e_i(B)$
-- statement:
--   Fix a matroid game, a profile $B$, a player $i$ and a resource $e$. The **admissible alternatives** are the resources $f\in E$ with $B_i+f-e\in\mathcal B_i$.
--
--   1. The **cost of the cheapest alternative** of player $i$ to $e$ is
--   $$\Delta^e_i(B)=\min_{f\in E,\ B_i+f-e\in\mathcal B_i}\bigl(c_f(B_i+f-e,B_{-i})+d_{i,f}\bigr),$$
--   where $c_f(B')=c_f(N_f(B'))$.
--   2. The **virtual cost value** of resource $e$ for player $i$ is $\pi^e_i=c_e(\{i\})+d_{i,e}$; it does not depend on the profile.
--   3. The **virtual deviation cost** is
--   $$\bar\Delta^e_i(B)=\min_{f\in E,\ B_i+f-e\in\mathcal B_i}\pi^f_i.$$
--
--   $\Delta$ enters the characterization of enforceable profiles (Lemma 3), and Algorithm 1 tests that characterization with the smaller virtual values $\bar\Delta$.
--
--   **Formalization Note** $B_i+f-e$ is $(B_i\setminus\{e\})\cup\{f\}$, so for $e\in B_i$ the resource $f=e$ is admissible and both minima are over a nonempty finite set. Lean's definitions return $0$ when no alternative is admissible; that case does not arise for a profile $B$ and $e\in B_i$, the only case in which the paper uses $\Delta^e_i(B)$ and $\bar\Delta^e_i(B)$.
-- source:
--   Harks, Hoefer, Huber & Surek, Efficient Black-Box Reductions for Separable Cost Sharing, arXiv:1802.10351v1, §3, p.6 (Δᵉᵢ(B), πᵉᵢ), p.7 (Δ̄ᵉᵢ(B))

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame

namespace SepCostShare

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

open Classical in
/-- The **admissible alternatives** of player `i` to resource `e` at profile `B`,
arXiv:1802.10351v1, §3, p.6: the `f ∈ E` with `Bᵢ + f − e ∈ 𝓑ᵢ`, the index set of the minima
defining `Δᵉᵢ(B)` and `Δ̄ᵉᵢ(B)`.

**Formalization Note.** `Bᵢ + f − e` is `(Bᵢ ∖ {e}) ∪ {f}`, so for `e ∈ Bᵢ` the resource `f = e`
itself is admissible and the set is nonempty. -/
noncomputable def MatroidGame.alts (G : MatroidGame N E) (B : N → Finset E) (i : N) (e : E) :
    Finset E :=
  Finset.univ.filter fun f => (G.M i).IsBase (↑(insert f ((B i).erase e)) : Set E)

/-- **Cost of the cheapest alternative**, arXiv:1802.10351v1, §3, p.6:
`Δᵉᵢ(B) := min_{f∈E, Bᵢ+f−e∈𝓑ᵢ} (c_f(Bᵢ + f − e, B₋ᵢ) + dᵢ,f)`, with
`c_f(B′) = c_f(N_f(B′))`.

**Formalization Note.** The minimum is a `Finset.inf'` over `alts`; the fallback value `0` for an
empty index set is never reached when `B` is a profile and `e ∈ Bᵢ` (then `e ∈ alts`), which is
the only case in which the paper uses `Δᵉᵢ(B)`. -/
noncomputable def MatroidGame.delta (G : MatroidGame N E) (B : N → Finset E) (i : N) (e : E) :
    ℝ :=
  if h : (G.alts B i e).Nonempty then
    (G.alts B i e).inf' h fun f => G.c f (G.users f (G.swap B i e f)) + G.d i f
  else 0

/-- **Virtual cost value**, arXiv:1802.10351v1, p.6: `πᵉᵢ = cₑ({i}) + dᵢ,ₑ`. -/
def MatroidGame.pi (G : MatroidGame N E) (i : N) (e : E) : ℝ :=
  G.c e {i} + G.d i e

/-- **Virtual deviation cost**, arXiv:1802.10351v1, p.7: `Δ̄ᵉᵢ(B) = min_{f∈E, Bᵢ+f−e∈𝓑ᵢ} πᶠᵢ`.

**Formalization Note.** As for `delta`, the fallback `0` on an empty index set is never reached
when `B` is a profile and `e ∈ Bᵢ`. -/
noncomputable def MatroidGame.deltaBar (G : MatroidGame N E) (B : N → Finset E) (i : N)
    (e : E) : ℝ :=
  if h : (G.alts B i e).Nonempty then (G.alts B i e).inf' h fun f => G.pi i f else 0

end SepCostShare


