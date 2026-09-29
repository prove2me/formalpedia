-- Prove2me | Definitions.Def_HighDimProb_Chaining_ProcessESup
-- name    : HighDimProb_Chaining_ProcessESup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:02:24.940988+00:00
-- url     : https://prove2.me/theorems/786f09be-4544-4979-95fc-2c42d656526c
-- title:
--   The expected supremum $E \sup_{t\in T} X_t$ of a random process
-- statement:
--   This is the **expected supremum** of a random process, the quantity Dudley's integral
--   inequality (Theorem 8.1.3) bounds above.
--
--   Fix a probability space $(\Omega,\mathcal F,P)$ and a family $(X_t)_{t\in T}$ of real random
--   variables indexed by an arbitrary (possibly uncountable) set $T$. Since $\sup_{t\in T}
--   X_t(\omega)$ need not be a measurable function of $\omega$ for a general $T$, this is defined
--   through the process's finite-dimensional marginals, following Vershynin's own convention set
--   in Section 7.2:
--
--   $$
--   E \sup_{t\in T} X_t \;:=\; \sup_{T_0 \subseteq T \text{ finite, nonempty}} E \max_{t\in T_0} X_t.
--   $$
--
--   **Formalization Note** Valued in `EReal`, not `ℝ`: a real-valued supremum would silently
--   default to the junk value $0$ when the set of finite marginals is unbounded above, making a
--   comparison against it vacuous. This is this chunk's own copy of the same-named definition
--   already built for `06-gaussian-processes`: that chunk's copy is still a draft (not in
--   `missions/README.md`'s published-definitions list), so per `CAPTAIN_BRIEF.md` Addendum 2 rule
--   5 it is redefined here rather than imported.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 160, footnote 3 to Section 7.2; used as the LHS of Theorem 8.1.3, p. 188

import Mathlib

open MeasureTheory

namespace HighDimProb.Chaining

/-- The **expected supremum** `E sup_{t∈T} X_t` of a random process `(X_t)_{t∈T}` on a
probability space `(Ω, P)`, understood through the process's finite-dimensional marginals, exactly
as Vershynin's own footnote 3 to Section 7.2 (p. 160, PDF p. 168) sets the convention for the
whole book (Chapter 8's Theorem 8.1.3 uses `E sup_{t∈T} X_t` for a general, possibly uncountable,
index set `T`):

`E sup_{t∈T} X_t := sup { E max_{t∈T0} X_t : T0 ⊆ T finite and nonempty }`.

Valued in `EReal`, not `ℝ`, for the same reason as the definition of the same name built for
`06-gaussian-processes` (`HighDimProb.RandomProcesses.processESup`): a real-valued `sSup` would
silently default to the junk value `0` whenever the underlying set of finite marginals is
unbounded above, making a comparison against it vacuous. That chunk's copy is a still-draft
definition (not in `missions/README.md`'s published list), so per `CAPTAIN_BRIEF.md` Addendum 2
rule 5 this chapter redefines its own copy rather than importing it. -/
noncomputable def processESup {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {T : Type}
    (X : T → Ω → ℝ) : EReal :=
  ⨆ (T0 : {s : Finset T // s.Nonempty}), ((∫ ω, T0.1.sup' T0.2 (fun t => X t ω) ∂P : ℝ) : EReal)

end HighDimProb.Chaining


