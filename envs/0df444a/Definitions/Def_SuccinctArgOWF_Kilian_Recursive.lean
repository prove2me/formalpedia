-- Prove2me | Definitions.Def_SuccinctArgOWF_Kilian_Recursive
-- name    : SuccinctArgOWF_Kilian_Recursive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:19.202218+00:00
-- url     : https://prove2.me/theorems/fa877c0b-ab7e-4dc3-8a77-d4c37c055917
-- title:
--   Construction 5.3, the overhead $V$, the hybrids $\mathrm{Hyb}_{1,k}$ and the events $F_i, D_i$
-- statement:
--   Let $\mathrm{Com}_{\mathrm{in}}$ be a $c$-round public-coin scheme with interval opening for $\{0,1\}^N$ whose sender messages lie in $\{0,1\}^d$ (local verification w.r.t. $J$), and $\mathrm{Com}_{\mathrm{out}}$ an $\ell$-round scheme with interval opening for $\{0,1\}^d$.
--
--   **Construction 5.3.** On $m\in\{0,1\}^N$, for $i=1,\dots,c$: the receiver sends $r_i\leftarrow R_{\mathrm{in},i}$ (together with its first message of the $i$-th outer commitment); the sender computes $(y_i,\mathrm{state}_{\mathrm{in},i})=S_{\mathrm{in},i}(\mathrm{state}_{\mathrm{in},i-1},r_i)$, keeps $y_i$, and both run the outer commitment $\langle S_{\mathrm{out}}(y_i),R_{\mathrm{out}}(\rho_i)\rangle$. The scheme has $c\ell$ rounds. An opening of $I$ is $\pi=(\pi_{\mathrm{in}},(u_i,\sigma_i)_{i\in[c]})$ with $\pi_{\mathrm{in}}=\mathrm{Open}_{\mathrm{in}}(\mathrm{state}_{\mathrm{in},c},I)$, $u_i=(y_i)_{J(I)}$, $\sigma_i=\mathrm{Open}_{\mathrm{out}}(\mathrm{state}_{\mathrm{out},i},J(I))$, and $\mathrm{Ver}$ accepts iff
--
--   $$\mathrm{Ver}_{\mathrm{out}}(\rho_i,\tau_i,J(I),u_i,\sigma_i)=1\ \ (i\in[c])\quad\text{and}\quad \mathrm{Ver}_{\mathrm{in}}(\vec r,(u_1,\dots,u_c),I,v,\pi_{\mathrm{in}})=1 .$$
--
--   **Overhead and $t_\varepsilon$.** $V=V(t)$ bounds the overhead (Theorem 5.2) if one program of total cost at most $V$ per task samples the receiver messages of one execution exactly uniformly, computes $J(I)$, and checks two candidate openings of a time-$t$ adversary, returning both verdicts and the revealed inner restrictions. $t_\varepsilon=\lfloor C\,c^2(t+V+d)/\varepsilon\rfloor$ is the bound $O(c^2(t+V+d)/\varepsilon)$ with the constant $C$.
--
--   **Hybrids (p. 16).** $\mathrm{Hyb}_0(A)$ is the selective interval binding game of the scheme; $A$ wins $\mathrm{Hyb}_{1,k}$ if it wins $\mathrm{Hyb}_0$ and its openings $\pi,\pi'$ satisfy $u_i=u'_i$ for all $i\le k$; $\mathrm{Hyb}_1=\mathrm{Hyb}_{1,c}$.
--
--   **Events of Proposition 5.6 (p. 17).** $Q=\lceil c/\varepsilon\rceil$. With the random tape $\omega$ of $A$ fixed, the real receiver coins, and $Q$ independent continuations at the real prefix $\gamma_i$ through outer commitment $i$ (real coins before, fresh coins after), $E$ is the event that $A$ wins $\mathrm{Hyb}_1$; $F_i$: the real execution satisfies $E$ but all $Q$ trials fail; $D_i$: the real execution satisfies $E$, a successful trial is found, and the value $\hat u_i$ of its first opening differs from the real $u_i$.
--
--   These are the objects of Theorem 5.2, Lemma 5.4, Propositions 5.5–5.6 and Claims 5.6.1–5.6.2.
--
--   **Formalization Note** The pair $(r_i,\rho_{i,1})$ is sent as one self-delimiting string. $\mathrm{Ver}_{\mathrm{in}}(\vec r,\vec u,\dots)$ is evaluated on the messages that carry $u_i$ at $J(I)$ and zeros elsewhere, which local verification makes independent of the choice; $u_i$ must have $|J(I)|$ bits. "Openings of a time-$t$ adversary" covers every output such an adversary can produce in the machine model: an output component is read from a tape that may already hold an input of the invocation, so openings have at most $2t$ bits and a sender message $\tau_k$ at most $t+|r_k|$ bits.
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), Construction 5.3, pp. 13–14 (PDF pp. 15–16); Theorem 5.2, p. 13; proof of Lemma 5.4, pp. 15–18 (PDF pp. 17–20)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_Commit

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-! # The recursive commitment (Construction 5.3), the overhead `V` of Theorem 5.2, the hybrids of
Lemma 5.4 and the events `F_i`, `D_i` of Proposition 5.6

Throughout, `Com_in` is a `c`-round scheme with interval opening for messages in `{0,1}^N` whose
sender messages lie in `{0,1}^d` (local verification w.r.t. `J`), and `Com_out` an `ℓ`-round scheme
with interval opening for messages in `{0,1}^d` (`d = Com_out.N`). Round `k ∈ [cℓ]` of the
recursive scheme is round `j` of iteration `i`, `k ↔ (i, j)` (both indexed from `0` in Lean). -/

/-- Iteration and round of a round index of Construction 5.3. -/
def splitIdx {c ℓ : ℕ} (k : Fin (c * ℓ)) : Fin c × Fin ℓ := finProdFinEquiv.symm k

/-- The round index of round `j` of iteration `i`. -/
def joinIdx {c ℓ : ℕ} (i : Fin c) (j : Fin ℓ) : Fin (c * ℓ) := finProdFinEquiv (i, j)

/-- The receiver's first message of iteration `i`, which carries `(r_i, first message of ρ_i)`. -/
def firstPair (c ℓ : ℕ) (s : Fin (c * ℓ) → Str) (i : Fin c) : List Str :=
  if h : 0 < ℓ then (decList (s (joinIdx i ⟨0, h⟩))).getD [] else []

/-- The parts of an opening `π = (π_in, (u_i, σ_i)_{i ∈ [c]})` of Construction 5.3: `π_in` and the
list `[u₁, σ₁, …, u_c, σ_c]`. -/
def openParts (π : Str) : Str × List Str :=
  (((decList π).getD []).getD 0 [], (decList (((decList π).getD []).getD 1 [])).getD [])

/-- The revealed inner-message restriction `u_i` (index `i` from `0`) of an opening. -/
def openU (π : Str) (i : ℕ) : Str := (openParts π).2.getD (2 * i) []

open Classical in
/-- Construction 5.3 (p.13–14). Round `(i, 0)` sends `(r_i, ρ_{i,1})` encoded as
`encList [r_i, ρ_{i,1}]`; the sender computes `(y_i, state_in,i) = S_in,i(state_in,i−1, r_i)`,
keeps `y_i` and runs the outer commitment on `y_i`. `Open(state, I) = (π_in, (u_i, σ_i)_{i∈[c]})` with
`π_in = Open_in(state_in,c, I)`, `u_i = (y_i)_{J(I)}`, `σ_i = Open_out(state_out,i, J(I))`. `Ver`
accepts iff every `Ver_out(ρ_i, τ_i, J(I), u_i, σ_i) = 1` (with `u_i ∈ {0,1}^{|J(I)|}`) and
`Ver_in(r⃗, (u₁, …, u_c), I, v, π_in) = 1`, the latter evaluated (as local verification allows) on the
messages holding `u_i` at `J(I)` and zeros elsewhere. -/
noncomputable def constr53 (Ci Co : ICommit) (J : ℕ → ℕ → ℕ × ℕ) : ICommit where
  N := Ci.N
  ℓ := Ci.ℓ * Co.ℓ
  R := fun k =>
    if (splitIdx k).2.1 = 0 then
      ((Ci.R (splitIdx k).1) ×ˢ (Co.R (splitIdx k).2)).image fun p => encList [p.1, p.2]
    else Co.R (splitIdx k).2
  R_ne := fun k => by
    split_ifs
    · exact ((Ci.R_ne _).product (Co.R_ne _)).image _
    · exact Co.R_ne _
  σ := Ci.σ × (ℕ → Str) × (ℕ → Co.σ)
  init := fun m => (Ci.init m, fun _ => [], fun _ => Co.init [])
  S := fun k st msg =>
    let i := (splitIdx k).1
    let j := (splitIdx k).2
    if j.1 = 0 then
      let r := ((decList msg).getD []).getD 0 []
      let ρ := ((decList msg).getD []).getD 1 []
      let y := (Ci.S i st.1 r).1
      let o := Co.S j (Co.init y) ρ
      (o.1, ((Ci.S i st.1 r).2, Function.update st.2.1 i.1 y, Function.update st.2.2 i.1 o.2))
    else
      let o := Co.S j (st.2.2 i.1) msg
      (o.1, (st.1, st.2.1, Function.update st.2.2 i.1 o.2))
  Open := fun st a b =>
    encList [Ci.Open st.1 a b, encList ((List.range Ci.ℓ).flatMap fun i =>
      [sub (st.2.1 i) (J a b).1 (J a b).2, Co.Open (st.2.2 i) (J a b).1 (J a b).2])]
  Ver := fun s τ a b v π =>
    let L := (openParts π).2
    let u : Fin Ci.ℓ → Str := fun i => L.getD (2 * i.1) []
    let σ : Fin Ci.ℓ → Str := fun i => L.getD (2 * i.1 + 1) []
    let r : Fin Ci.ℓ → Str := fun i => (firstPair Ci.ℓ Co.ℓ s i).getD 0 []
    let ρ : Fin Ci.ℓ → Fin Co.ℓ → Str := fun i j =>
      if j.1 = 0 then (firstPair Ci.ℓ Co.ℓ s i).getD 1 [] else s (joinIdx i j)
    decide (((decList π).getD []).length = 2 ∧ L.length = 2 * Ci.ℓ ∧
      (∀ i : Fin Ci.ℓ, (u i).length = (J a b).2 + 1 - (J a b).1 ∧
        Co.Ver (ρ i) (fun j => τ (joinIdx i j)) (J a b).1 (J a b).2 (u i) (σ i) = true) ∧
      Ci.Ver r (fun i => embed Co.N (J a b).1 (J a b).2 (u i)) a b v (openParts π).1 = true)

/-- `t_ε = ⌊C · c² (t + V + d) / ε⌋`, the time bound `O(c²(t + V + d)/ε)` of Theorem 5.2 / Lemma 5.4
with the constant `C`. -/
noncomputable def tEps (C c t V d : ℕ) (ε : ℝ) : ℕ :=
  ⌊(C : ℝ) * (c : ℝ) ^ 2 * ((t : ℝ) + V + d) / ε⌋₊

/-- `V = V(t)` bounds the overhead (Theorem 5.2): one adversary-style program `B` (a machine with
advice per task) of total cost at most `V` per task (codes, advice and steps) that
1. (phase `0`) samples the receiver messages of one execution of Construction 5.3 from `V` coins,
   exactly uniformly;
2. (phase `1`) computes `J(I)` from `I` (endpoints in binary);
3. (phase `2`) checks two candidate openings `(v, π)`, `(v', π')` of a sender transcript `τ`, for every
   output a time-`t` adversary can produce in this machine model: openings of length at most `2t` and
   messages `τ_k` of length at most `t + |r_k|` (an output component is read from a tape that may
   already hold an input of the invocation — the receiver message `r_k`, the random tape or the advice,
   each of length at most `t` except `r_k` — extended by at most `t` written cells): it outputs both
   verdicts of `Ver` and the revealed inner-message restrictions `u⃗`, `u⃗'` of the two openings. -/
def IsOverheadBound (Ci Co : ICommit) (J : ℕ → ℕ → ℕ × ℕ) (t V : ℕ) : Prop :=
  let Com := constr53 Ci Co J
  ∃ B : Adv,
    (∀ ω : Str, ω.length = V → ∃ s os, B.run ω [] [(0, [])] [] = some (s, os) ∧
      B.descCost + s ≤ V) ∧
    (∀ s₀ : Com.Coins, ((Finset.univ.filter fun ω : Fin V → Bool =>
        outC (B.outs (List.ofFn ω) [] [(0, [])]) 0 1 = encList (List.ofFn (Com.cs s₀))).card) *
        Fintype.card Com.Coins = 2 ^ V) ∧
    (∀ a b, IsInterval Ci.N a b → ∃ s os,
      B.run [] [] [(1, encList [natBits a, natBits b])] [] = some (s, os) ∧ B.descCost + s ≤ V ∧
        outC os 0 1 = natBits (J a b).1 ∧ outC os 0 2 = natBits (J a b).2) ∧
    (∀ (s₀ : Com.Coins) (τ : Fin Com.ℓ → Str) (a b : ℕ) (v π v' π' : Str),
      (∀ k, (τ k).length ≤ t + (Com.cs s₀ k).length) → v.length ≤ 2 * t → π.length ≤ 2 * t →
      v'.length ≤ 2 * t → π'.length ≤ 2 * t →
      ∃ s os, B.run [] [] [(2, encList [encList (List.ofFn (Com.cs s₀)), encList (List.ofFn τ),
          natBits a, natBits b, v, π, v', π'])] [] = some (s, os) ∧ B.descCost + s ≤ V ∧
        outC os 0 1 = [Com.Ver (Com.cs s₀) τ a b v π, Com.Ver (Com.cs s₀) τ a b v' π'] ∧
        outC os 0 2 = encList ((List.range Ci.ℓ).map (openU π)) ∧
        outC os 0 3 = encList ((List.range Ci.ℓ).map (openU π')))

/-- The two openings `π`, `π'` (components `2` and `4` of the final invocation) produced by `A` in the
selective interval binding game of `Com` on coins `ω, s`. -/
noncomputable def proofsOf (Com : ICommit) (A : Adv) (t : ℕ) (ω : Fin t → Bool) (s : Com.Coins) :
    Str × Str :=
  let os := A.outs (List.ofFn ω) [] (Com.selSched s)
  (outC os (Com.ℓ + 1) 2, outC os (Com.ℓ + 1) 4)

/-- `A` wins `Hyb_{1,k}` (p.16): it wins `Hyb₀` (the selective interval binding game of
Construction 5.3) and its two openings reveal the same parts of the first `k` inner messages,
`u_i = u'_i` for all `i ≤ k`. `Hyb_{1,0} = Hyb₀`; `Hyb₁ = Hyb_{1,c}`. -/
noncomputable def hybWin (Ci Co : ICommit) (J : ℕ → ℕ → ℕ × ℕ) (k : ℕ) (A : Adv) (t : ℕ)
    (ω : Fin t → Bool) (s : (constr53 Ci Co J).Coins) : Prop :=
  (constr53 Ci Co J).selWin false A t ω s ∧
    ∀ i < k, openU (proofsOf _ A t ω s).1 i = openU (proofsOf _ A t ω s).2 i

/-- `Pr[Hyb_{1,k}(A)]`. -/
noncomputable def hybProb (Ci Co : ICommit) (J : ℕ → ℕ → ℕ × ℕ) (k : ℕ) (A : Adv) (t : ℕ) : ℝ :=
  prob fun p : (Fin t → Bool) × (constr53 Ci Co J).Coins => hybWin Ci Co J k A t p.1 p.2

/-- `Q = ⌈c/ε⌉`, the cap on the number of continuations (proof of Lemma 5.4). -/
noncomputable def capQ (c : ℕ) (ε : ℝ) : ℕ := ⌈(c : ℝ) / ε⌉₊

/-- The receiver coins of a continuation at the real prefix through outer commitment `i` (iterations
`1, …, i`, i.e. rounds `< iℓ`): the real coins `s` there, the fresh coins `s'` afterwards. -/
def mixCoins (Ci Co : ICommit) (J : ℕ → ℕ → ℕ × ℕ) (i : ℕ) (s s' : (constr53 Ci Co J).Coins) :
    (constr53 Ci Co J).Coins :=
  fun k => if k.1 < i * Co.ℓ then s k else s' k

/-- The probability space of the reduction `A'` of Proposition 5.6 at extraction step `i`: the
random tape `ω` of `A` (fixed throughout all rewindings), the real receiver coins `s`, and the fresh
receiver coins of `Q` independent continuations. -/
abbrev ExtrSpace (Ci Co : ICommit) (J : ℕ → ℕ → ℕ × ℕ) (t Q : ℕ) :=
  (Fin t → Bool) × (constr53 Ci Co J).Coins × (Fin Q → (constr53 Ci Co J).Coins)

/-- `F_i` (p.17), for `1 ≤ i < c`: the real execution satisfies `E` (`A` wins `Hyb₁`) but all `Q`
trials at the real prefix through outer commitment `i` fail. -/
def eventF (Ci Co : ICommit) (J : ℕ → ℕ → ℕ × ℕ) (A : Adv) (t Q i : ℕ)
    (p : ExtrSpace Ci Co J t Q) : Prop :=
  hybWin Ci Co J Ci.ℓ A t p.1 p.2.1 ∧
    ∀ q : Fin Q, ¬ hybWin Ci Co J Ci.ℓ A t p.1 (mixCoins Ci Co J i p.2.1 (p.2.2 q))

/-- `D_i` (p.17), for `1 ≤ i < c`: the real execution satisfies `E`, a successful trial is found, and
the value `û_i` extracted from the first opening of the first successful trial differs from the real
value `u_i` (the `i`-th revealed inner restriction of the real first opening). -/
noncomputable def eventD (Ci Co : ICommit) (J : ℕ → ℕ → ℕ × ℕ) (A : Adv) (t Q i : ℕ)
    (p : ExtrSpace Ci Co J t Q) : Prop :=
  hybWin Ci Co J Ci.ℓ A t p.1 p.2.1 ∧
    ∃ q : Fin Q, hybWin Ci Co J Ci.ℓ A t p.1 (mixCoins Ci Co J i p.2.1 (p.2.2 q)) ∧
      (∀ q' : Fin Q, q' < q →
        ¬ hybWin Ci Co J Ci.ℓ A t p.1 (mixCoins Ci Co J i p.2.1 (p.2.2 q'))) ∧
      openU (proofsOf _ A t p.1 (mixCoins Ci Co J i p.2.1 (p.2.2 q))).1 (i - 1) ≠
        openU (proofsOf _ A t p.1 p.2.1).1 (i - 1)

end SuccinctArgOWF.Kilian


