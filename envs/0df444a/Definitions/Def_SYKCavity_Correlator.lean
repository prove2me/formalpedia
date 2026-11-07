-- Prove2me | Definitions.Def_SYKCavity_Correlator
-- name    : SYKCavity_Correlator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:30.906067+00:00
-- url     : https://prove2.me/theorems/21505841-342d-4a53-8cec-9b281a2a7c4c
-- title:
--   The correlators $\langle\chi_{j_1}(t_1)\cdots\chi_{j_d}(t_d)\rangle_N$, products of $Q_{uv}$, and the centered moments $\mu_p$
-- statement:
--   Fix $\beta$, $N$ and Section 3's Hamiltonian $H$. For sites $j_1,\dots,j_d$ and distinct times $1>t_1>\dots>t_d>0$,
--   $$\langle\chi_{j_1}(t_1)\cdots\chi_{j_d}(t_d)\rangle_N=\frac{\mathbb E_J\operatorname{Tr}\bigl[e^{(1-t_1)\beta H}\psi_{j_1}e^{(t_1-t_2)\beta H}\psi_{j_2}\cdots\psi_{j_d}e^{t_d\beta H}\bigr]}{\mathbb E_J\operatorname{Tr}e^{\beta H}}\qquad(3.20)$$
--   (a ratio of disorder averages). Other orders of distinct times are first reordered decreasingly, with the sign of the permutation (E.1). Following Lemma 42:
--
--   1. **equal times** are evaluated by the *alternating* prescription: the operators of each equal-time group are replaced by their antisymmetrization $\frac1{q!}\sum_\sigma\operatorname{sgn}(\sigma)\psi_{j_{a_{\sigma(1)}}}\cdots\psi_{j_{a_{\sigma(q)}}}$ (E.3); equivalently the value is the average, over all relative orders of the occurrences, of the **ordered limits** at $t+\varepsilon\eta$, $\varepsilon\downarrow0$, with distinct offsets $\eta$;
--   2. **times on the thermal circle** (any reals, including $0$ and $1$): choose $c\in[0,1)$ different from every $t_a\bmod1$, put $k_a=\lfloor t_a-c\rfloor$ and $\tau_a=t_a-c-k_a\in(0,1)$, and multiply the value at $\tau$ by $(-1)^{\sum_ak_a}$ (E.4).
--
--   The **collective variables** $Q_{uv}=\frac1{2N}\sum_i\chi_i(u)\chi_i(v)$ (3.16) enter by linearity:
--   $$\Bigl\langle F\prod_{l=1}^LQ_{u_lv_l}\Bigr\rangle_N=\frac1{(2N)^L}\sum_{i_1,\dots,i_L}\bigl\langle F\,\chi_{i_1}(u_1)\chi_{i_1}(v_1)\cdots\chi_{i_L}(u_L)\chi_{i_L}(v_L)\bigr\rangle_N,$$
--   and the **centered moments** (4.7) are
--   $$\mu_p\bigl((u_1,v_1),\dots,(u_p,v_p)\bigr)=\Bigl\langle\prod_{r=1}^p\bigl(Q_{u_rv_r}-G_*(u_r,v_r)\bigr)\Bigr\rangle_N=\sum_{S\subseteq[p]}(-1)^{p-|S|}\prod_{r\notin S}G_*(u_r,v_r)\Bigl\langle\prod_{r\in S}Q_{u_rv_r}\Bigr\rangle_N,$$
--   with the coincident-time limit taken in the entire centered expression (E.10); $\mu_0=1$. The ordered-limit versions (`ordVal`, `qOrd`, `muOrd`) are defined too, since Lemma 43 and Corollary 6 are also stated for them.
--
--   These are the quantities the algorithm computes: $F_{O;A}$ in (4.1) reduces to them by (3.20), Lemma 43 reconstructs them from moments of $Q$, and the hierarchy (4.9) determines the $\mu_p$.
--
--   **Formalization Note** The page defines $\langle\cdot\rangle_N$ as a ratio of Grassmann integrals (3.19) and proves (3.20) and Lemma 42; here the trace-side expression is the definition. The cut is the least $c=k/(d+1)$, $k\in\{0,\dots,d\}$, avoiding all $t_a\bmod1$ (so $c=0$ for times in $(0,1)$). Expectations are Bochner integrals under the Gaussian law; values are complex.
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), (3.16), p.22; (3.19)–(3.20), p.23; (4.7)–(4.8), p.26; Lemma 42, (E.1)–(E.4), p.95; (E.10)–(E.11), p.96

import Mathlib
import Definitions.Def_SYKCavity_Majorana
import Definitions.Def_SYKCavity_Saddle

open MeasureTheory

namespace SYKCavity

/-!
# The collective correlators `⟨χ_{j_1}(t_1) ⋯ χ_{j_d}(t_d)⟩_N`, products of `Q`, and the centered
moments `μ_p`

A. Schmidhuber, A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass
transition*, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5): (3.16), p.22; (3.19)–(3.20),
p.23; (4.7)–(4.8), p.26; Lemma 42, (E.1)–(E.4), p.95; (E.10)–(E.11), p.96.

The page defines `⟨·⟩_N` as a ratio of Grassmann integrals (3.19) and proves (3.20) and Lemma 42,
which express it through disorder-averaged traces. Here `⟨·⟩_N` is **defined** by that trace-side
expression, with Lemma 42's prescriptions.

**Formalization Note.**
* All operators use Section 3's Hamiltonian `H = √(3/(8N³)) Σ_A J_A Γ_A` (`Hgamma`), and every
  expectation `E_J` is the Bochner integral against `gaussLaw N`. A correlator is the ratio of
  disorder averages `E_J Tr[⋯] / E_J Tr e^{βH}` (3.20), not the average of a ratio. Values are complex.
* An occurrence list is `d` Grassmann variables `χ_{j_a}(t_a)`, `a ∈ Fin d`, in the index order of
  `Fin d`, with sites `j : Fin d → Fin N` and real times `t` (points of the thermal circle `ℝ/ℤ`).
* Thermal circle (E.4): `cut t = c` is the least `k/(d+1)`, `k ∈ {0, …, d}`, different from every
  `t_a mod 1` (it exists by pigeonhole; it is `0` when no `t_a` is an integer), `wind t a = ⌊t_a − c⌋`,
  `reduced t a = t_a − c − ⌊t_a − c⌋ ∈ (0, 1)`, and the value is `(−1)^{Σ_a ⌊t_a − c⌋}` times the value
  at the reduced times. For `t ∈ (0,1)^d` with no time `0`, `c = 0` and nothing changes.
* Ordered values: offsets `η : Fin d → ℝ` order the occurrences by decreasing reduced time, ties by
  decreasing offset (the ordered limit `t + εη`, `ε ↓ 0`, of Lemma 42); with that order `π`, (E.1) is
  `sgn(π) Tr(e^{(1−τ_{π(1)})βH} ψ_{j_{π(1)}} e^{(τ_{π(1)}−τ_{π(2)})βH} ⋯ ψ_{j_{π(d)}} e^{τ_{π(d)}βH})`,
  disorder-averaged and divided by `E_J Tr e^{βH}`. At equal times the gap exponential is `e^0 = I`.
  The sign `sgn(π)` is `(−1)` to the number of inversions. A mask `m` replaces the unmasked
  occurrences by `I` (keeping their positions) and drops them from the sign and the winding.
* Alternating values (E.2)–(E.3): the average of the ordered values over all `d!` relative orders
  of the offsets, i.e. over offsets `η = ρ` for `ρ ∈ S_d`. Within an equal-time group of size `q` each
  order has weight `1/q!` and sign `sgn`, which is the independent antisymmetrization (E.3). This is
  `⟨χ_{j_1}(t_1) ⋯ χ_{j_d}(t_d)⟩_N` (`altVal`).
* Collective variables (3.16), (E.10): `⟨χ_{j}(t) ∏_{l<L} Q_{u_l v_l}⟩_N` is
  `(2N)^{−L} Σ_{i : Fin L → Fin N}` of the correlator of the list `χ_{j_1}(t_1) ⋯ χ_{j_m}(t_m)` followed
  by `χ_{i_1}(u_1)χ_{i_1}(v_1) ⋯ χ_{i_L}(u_L)χ_{i_L}(v_L)`; `qOrd` uses offsets for every occurrence,
  `qAlt` the alternating value.
* Centered moments (4.7), (E.10): `μ_p((u_1,v_1), …, (u_p,v_p)) = ⟨∏_r (Q_{u_r v_r} − G*(u_r, v_r))⟩_N
  = Σ_{S ⊆ [p]} (−1)^{p−|S|} ∏_{r ∉ S} G*(u_r, v_r) ⟨∏_{r ∈ S} Q_{u_r v_r}⟩_N`, the limit being taken
  in the entire centered expression: `muOrd` evaluates every factor at the same ordered limit
  (`G*` by `gOrd`), and `muAlt` (the page's `μ_p`) averages `muOrd` over all relative orders of the
  `2p` occurrences. `μ_0 = 1`.
-/

/-- The disorder-averaged thermal ratio `E_J[Tr W(J)] / E_J[Tr e^{βH}]`. -/
noncomputable def avgRatio (β : ℝ) (N : ℕ) (W : (Quad N → ℝ) → MOp N) : ℂ :=
  (∫ J, (W J).trace ∂gaussLaw N) / (∫ J, (expH β N J 1).trace ∂gaussLaw N)

/-- `e^{(1−τ_{π(1)})βH} op_{π(1)} e^{(τ_{π(1)}−τ_{π(2)})βH} ⋯ op_{π(d)} e^{τ_{π(d)}βH}`. -/
noncomputable def thermalWord (β : ℝ) (N : ℕ) (J : Quad N → ℝ) {d : ℕ} (τ : Fin d → ℝ)
    (π : Equiv.Perm (Fin d)) (op : Fin d → MOp N) : MOp N :=
  let tt : ℕ → ℝ := fun k => if h : k < d then τ (π ⟨k, h⟩) else 0
  expH β N J (1 - tt 0) *
    ((List.finRange d).map (fun k => op (π k) * expH β N J (tt k.val - tt (k.val + 1)))).prod

/-- The index `k` of the cut `c = k/(d+1)`: the least `k` with `k/(d+1) ≠ t_a mod 1` for all `a`. -/
noncomputable def cutIndex {d : ℕ} (t : Fin d → ℝ) : ℕ :=
  sInf {k : ℕ | ∀ a, Int.fract (t a) ≠ (k : ℝ) / (d + 1)}

/-- The cut `c ∈ [0, 1)` of (E.4). -/
noncomputable def cut {d : ℕ} (t : Fin d → ℝ) : ℝ := (cutIndex t : ℝ) / (d + 1)

/-- The winding `k_a = ⌊t_a − c⌋` of (E.4). -/
noncomputable def wind {d : ℕ} (t : Fin d → ℝ) (a : Fin d) : ℤ := ⌊t a - cut t⌋

/-- The reduced time `τ_a = t_a − c − k_a ∈ (0, 1)` of (E.4). -/
noncomputable def reduced {d : ℕ} (t : Fin d → ℝ) (a : Fin d) : ℝ := t a - cut t - wind t a

/-- The order of the occurrences: decreasing time, ties by decreasing offset (then by index). -/
noncomputable def occOrder {d : ℕ} (τ η : Fin d → ℝ) : Equiv.Perm (Fin d) :=
  Tuple.sort (fun a => toLex (-τ a, -η a))

/-- The ordered value, with offsets `η`, of the product of the masked occurrences `χ_{j_a}(t_a)`
(`m a = true`) in index order: (E.4) applied to (E.1) at the ordered limit. -/
noncomputable def ordVal (β : ℝ) (N : ℕ) {d : ℕ} (j : Fin d → Fin N) (m : Fin d → Bool)
    (t η : Fin d → ℝ) : ℂ :=
  let τ := reduced t
  let π := occOrder τ η
  let inv := ((Finset.univ : Finset (Fin d × Fin d)).filter
    (fun x => x.1 < x.2 ∧ m x.1 = true ∧ m x.2 = true ∧ π.symm x.2 < π.symm x.1)).card
  (-1 : ℂ) ^ (∑ a ∈ Finset.univ.filter (fun a => m a = true), wind t a) * (-1 : ℂ) ^ inv *
    avgRatio β N (fun J => thermalWord β N J τ π (fun a => if m a then psi N (j a) else 1))

/-- `⟨χ_{j_1}(t_1) ⋯ χ_{j_d}(t_d)⟩_N`: the alternating value (E.2)–(E.4), the average of the
ordered values over all relative orders of the occurrences. -/
noncomputable def altVal (β : ℝ) (N : ℕ) {d : ℕ} (j : Fin d → Fin N) (t : Fin d → ℝ) : ℂ :=
  (Fintype.card (Equiv.Perm (Fin d)) : ℂ)⁻¹ *
    ∑ ρ : Equiv.Perm (Fin d), ordVal β N j (fun _ => true) t (fun a => ((ρ a : ℕ) : ℝ))

/-- The occurrence list `u_1, v_1, u_2, v_2, …` of `L` pairs (pair `l`, end `b`, at index `b + 2l`). -/
def pairList {α : Type*} {L : ℕ} (u v : Fin L → α) : Fin (L * 2) → α := fun a =>
  if (finProdFinEquiv.symm a).2 = 0 then u (finProdFinEquiv.symm a).1 else v (finProdFinEquiv.symm a).1

/-- `(2N)^{−L} Σ_i` of the ordered value of `χ_j(t) χ_{i_1}(u_1)χ_{i_1}(v_1) ⋯ χ_{i_L}(u_L)χ_{i_L}(v_L)`,
with one offset per occurrence: `⟨χ_{j_1}(t_1) ⋯ χ_{j_m}(t_m) ∏_l Q_{u_l v_l}⟩_N` at the ordered limit. -/
noncomputable def qOrd (β : ℝ) (N : ℕ) {m L : ℕ} (j : Fin m → Fin N) (t ηt : Fin m → ℝ)
    (u v ηu ηv : Fin L → ℝ) : ℂ :=
  ((2 * N : ℂ)⁻¹) ^ L * ∑ i : Fin L → Fin N,
    ordVal β N (Fin.append j (pairList i i)) (fun _ => true) (Fin.append t (pairList u v))
      (Fin.append ηt (pairList ηu ηv))

/-- `⟨χ_{j_1}(t_1) ⋯ χ_{j_m}(t_m) ∏_{l<L} Q_{u_l v_l}⟩_N` (alternating value), by (3.16) and (E.10). -/
noncomputable def qAlt (β : ℝ) (N : ℕ) {m L : ℕ} (j : Fin m → Fin N) (t : Fin m → ℝ)
    (u v : Fin L → ℝ) : ℂ :=
  ((2 * N : ℂ)⁻¹) ^ L * ∑ i : Fin L → Fin N,
    altVal β N (Fin.append j (pairList i i)) (Fin.append t (pairList u v))

/-- The centered moment `⟨∏_r (Q_{u_r v_r} − G*(u_r, v_r))⟩_N` at the ordered limit with offsets
`ηu`, `ηv` (every factor, including `G*`, at the same limit). -/
noncomputable def muOrd (β : ℝ) (N p : ℕ) (u v ηu ηv : Fin p → ℝ) : ℂ :=
  ∑ S : Finset (Fin p),
    (-1 : ℂ) ^ (p - S.card) * (∏ r ∈ Sᶜ, ((gOrd β (u r - v r) (ηu r - ηv r) : ℝ) : ℂ)) *
      qOrd β N (m := 0) Fin.elim0 Fin.elim0 Fin.elim0
        (u ∘ S.orderEmbOfFin rfl) (v ∘ S.orderEmbOfFin rfl)
        (ηu ∘ S.orderEmbOfFin rfl) (ηv ∘ S.orderEmbOfFin rfl)

/-- `μ_p((u_1,v_1), …, (u_p,v_p))`, (4.7): the alternating value of the centered moment, the average
of `muOrd` over all relative orders of the `2p` occurrences. -/
noncomputable def muAlt (β : ℝ) (N p : ℕ) (u v : Fin p → ℝ) : ℂ :=
  (Fintype.card (Equiv.Perm (Fin p × Fin 2)) : ℂ)⁻¹ *
    ∑ ρ : Equiv.Perm (Fin p × Fin 2),
      muOrd β N p u v (fun r => ((finProdFinEquiv (ρ (r, 0)) : ℕ) : ℝ))
        (fun r => ((finProdFinEquiv (ρ (r, 1)) : ℕ) : ℝ))

/-- The pairs `(u_r, v_r)_{r ≠ j}` in increasing index order. -/
def skip {α : Type*} {q : ℕ} (j : Fin q) (U : Fin q → α) : Fin (q - 1) → α := fun r =>
  U ⟨if r.val < j.val then r.val else r.val + 1, by
    have := r.isLt; have := j.isLt; split_ifs <;> omega⟩

end SYKCavity


