-- Prove2me | Definitions.Def_GroupIsoPoly_charSeries
-- name    : GroupIsoPoly_charSeries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:53:29.607874+00:00
-- url     : https://prove2.me/theorems/ae011472-b068-4a69-b105-6ac2fcf26b86
-- title:
--   The characteristic series $1=N_0<\cdots<N_j=\mathrm{srad}(Q)<\cdots<N_\ell=Q$
-- statement:
--   For a finite group $Q$ define subgroups $N_0,N_1,\dots$ by $N_0=1$ and
--   $$
--   N_{i+1}=\text{the preimage of }S(Q/N_i)\text{ under the quotient map }Q\to Q/N_i ,
--   $$
--   where $S$ is the selected characteristic subgroup ($\mathrm{AC}$ or the socle). The **length** $\ell$ of the series is the least $i$ with $N_i=Q$. The paper's series (9.3) is $1=N_0<\cdots<N_\ell=Q$; its terms are characteristic in $Q$, it passes through $\mathrm{srad}(Q)$, the factors below $\mathrm{srad}(Q)$ are elementary abelian, and $\ell\le\lfloor\log_2|Q|\rfloor$.
--
--   The series is the backbone of the group isomorphism algorithm: each elementary abelian factor is one group-extension step, and the cohomology transports work along it.
--
--   **Formalization Note** Each $N_i$ is normal, which is what makes $Q/N_i$ a group; the normality proof is carried along the recursion. The sequence is defined for all $i$ and stays at $Q$ after $\ell$.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), §9.2.1, (9.3), p.94 (PDF p.98)

import Mathlib
import Definitions.Def_GroupIsoPoly_AC

set_option autoImplicit false

namespace GroupIsoPoly

/-- The series as normal subgroups (the normality proof is carried so that the next quotient can be
formed): `N₀ = 1` and `N_{i+1}` is the preimage of `S(Q/N_i)`. -/
noncomputable def charSeriesAux (Q : Type*) [Group Q] : ℕ → {N : Subgroup Q // N.Normal}
  | 0 => ⟨⊥, inferInstance⟩
  | i + 1 =>
    haveI := (charSeriesAux Q i).2
    ⟨(S (Q ⧸ (charSeriesAux Q i).1)).comap (QuotientGroup.mk' (charSeriesAux Q i).1),
      Subgroup.Normal.comap inferInstance _⟩

/-- **The characteristic subgroup series** (9.3) `1 = N₀ < ⋯ < N_ℓ = Q`.

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), §9.2.1, p.94 (PDF p.98): "For an initial table group
Q, construct a series 1 = N0 < · · · < Nj = srad(Q) < · · · < Nℓ = Q (9.3) of subgroups
characteristic in Q … Define N_{i+1} as the preimage of S(Q/N_i) in Q."

`charSeries Q i` is `N_i`: `N₀ = 1`, and `N_{i+1}` is the preimage of `S(Q/N_i)` under the quotient
map `Q → Q/N_i`.

**Formalization Note.** The series is defined for every index; past `ℓ` it stays at `Q`
(`S` of the trivial group is trivial). -/
noncomputable def charSeries (Q : Type*) [Group Q] (i : ℕ) : Subgroup Q :=
  (charSeriesAux Q i).1

instance charSeries_normal (Q : Type*) [Group Q] (i : ℕ) : (charSeries Q i).Normal :=
  (charSeriesAux Q i).2

/-- The length `ℓ` of the series (9.3): the least `i` with `N_i = Q`. -/
noncomputable def seriesLength (Q : Type*) [Group Q] : ℕ :=
  sInf {i : ℕ | charSeries Q i = ⊤}

end GroupIsoPoly


