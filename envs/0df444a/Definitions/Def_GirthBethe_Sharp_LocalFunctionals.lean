-- Prove2me | Definitions.Def_GirthBethe_Sharp_LocalFunctionals
-- name    : GirthBethe_Sharp_LocalFunctionals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:53.290338+00:00
-- url     : https://prove2.me/theorems/52e262c1-5a46-4e5b-8a08-f2aba812aca5
-- title:
--   Definitions 2.1, 2.8, (3.6), §5.1 — the local functionals $H$, $H_c$, $S$, $F$, $\Gamma$ and deletion $q^{\setminus a}$
-- statement:
--   For a vector $q=(q_i)_{i\in\iota}$ indexed by a finite set $\iota$ (in the paper $\iota=[d]$; a probability vector is an element of the simplex $\Delta_d=\{q\in\mathbb R^d_{\ge0}:\sum_i q_i=1\}$), with natural logarithms and the convention $0\log0=0$:
--
--   1. the Shannon entropy $H(q)=-\sum_i q_i\log q_i$;
--   2. the complementary entropy functional $H_c(q)=-\sum_i(1-q_i)\log(1-q_i)$;
--   3. the local Bethe entropy functional $S(q)=H(q)-H_c(q)$;
--   4. for an ordering $\pi$ of the coordinates and a position $t$, the suffix mass $s^\pi_t(q)=\sum_{r\ge t}q_{\pi(r)}$, and the Anari–Rezaei functional
--   $$F(q)=\mathbb E_\pi\Big[\sum_{t}q_{\pi(t)}\log s^\pi_t(q)\Big]+H_c(q),$$
--   where $\pi$ is uniformly distributed over all orderings (for $\iota=[d]$, over $\mathrm{Sym}(d)$);
--   5. $\Gamma(q)=H(q)-2H_c(q)+2F(q)$ (equation (3.6));
--   6. for a coordinate $a$, the deletion $q^{\setminus a}=\big(q_i/(1-q_a)\big)_{i\ne a}$, a point of $\Delta_{d-1}$ when $q_a<1$, and the weighted term $(1-q_a)\Gamma(q^{\setminus a})$, interpreted as $0$ when $q_a=1$ (§5.1).
--
--   These are the vertex-local building blocks of the Bethe entropy and of the potentials used throughout the paper.
--
--   **Formalization Note** The functionals are defined on all real vectors (only their values on the simplex are used). $F$ is written in the second of the two equal forms of Definition 2.8; a term with $q_{\pi(t)}=0$ contributes $0$ (also when the suffix mass is $0$), so it agrees with the first form. Orderings are bijections $\mathrm{Fin}\,d\simeq\iota$ with 0-based positions.
--
--   The Shannon entropy is an alias of the published natural-log entropy `FuchsThesis.Types.entropy`; it adds no assumptions.
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 8, Definitions 2.1 (p. 6), 2.8 (p. 8), equation (3.6) (p. 10), §5.1 (p. 17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_FuchsThesis_Types_entropy

open Finset

namespace GirthBethe.Sharp

/-! Local functionals on a probability vector (Definitions 2.1, 2.8, equation (3.6), §5.1 of
Jain–Dong, STOC 2027 submission #705). A probability vector is indexed by a finite type `ι`;
`stdSimplex ℝ ι` is the simplex `Δ`. All logarithms are natural (`Real.log`), and
`Real.log 0 = 0` gives the convention `0 log 0 = 0`. -/

/-- Shannon entropy `H(q) = -∑ᵢ qᵢ log qᵢ` (Definition 2.1), reusing the published
natural-log entropy without any additional hypotheses. -/
noncomputable def shannon {ι : Type*} [Fintype ι] (q : ι → ℝ) : ℝ :=
  FuchsThesis.Types.entropy q

/-- Complementary entropy functional `Hc(q) = -∑ᵢ (1 - qᵢ) log (1 - qᵢ)` (Definition 2.1). -/
noncomputable def compEntropy {ι : Type*} [Fintype ι] (q : ι → ℝ) : ℝ :=
  ∑ i, -((1 - q i) * Real.log (1 - q i))

/-- Local Bethe entropy functional `S(q) = H(q) - Hc(q)` (Definition 2.1). -/
noncomputable def localBethe {ι : Type*} [Fintype ι] (q : ι → ℝ) : ℝ :=
  shannon q - compEntropy q

/-- Suffix mass `s_t^π(q) = ∑_{r ≥ t} q_{π(r)}` for an ordering `π : Fin d ≃ ι` of the
coordinates, read as the ordered list `π(0), …, π(d-1)` (Definition 2.8; positions are
0-based). -/
noncomputable def suffixMass {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (π : Fin (Fintype.card ι) ≃ ι) (t : Fin (Fintype.card ι)) : ℝ :=
  ∑ r : Fin (Fintype.card ι) with t ≤ r, q (π r)

/-- The Anari–Rezaei functional (Definition 2.8), in the source's second form
`F(q) = E_π[∑_t q_{π(t)} log s_t^π(q)] + Hc(q)`, with `π` uniformly distributed over all
orderings of the coordinates (for `ι = Fin d` these are exactly the permutations of `[d]`). -/
noncomputable def anariRezaei {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) : ℝ :=
  (1 / (Fintype.card (Fin (Fintype.card ι) ≃ ι) : ℝ)) *
      ∑ π : Fin (Fintype.card ι) ≃ ι, ∑ t, q (π t) * Real.log (suffixMass q π t) +
    compEntropy q

/-- `Γ(q) = H(q) - 2 Hc(q) + 2 F(q)` (equation (3.6)). -/
noncomputable def gammaFun {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) : ℝ :=
  shannon q - 2 * compEntropy q + 2 * anariRezaei q

/-- Deletion `q^{\a} = (qᵢ / (1 - q_a))_{i ≠ a}` (§5.1); a vector on `Δ_{d-1}` when `q_a < 1`. -/
noncomputable def deletion {ι : Type*} (q : ι → ℝ) (a : ι) : {i : ι // i ≠ a} → ℝ :=
  fun i => q i / (1 - q a)

/-- The weighted deletion term `(1 - q_a) Γ(q^{\a})`, interpreted as `0` when `q_a = 1` (§5.1). -/
noncomputable def weightedDeletion {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (a : ι) :
    ℝ :=
  if q a = 1 then 0 else (1 - q a) * gammaFun (deletion q a)

end GirthBethe.Sharp


