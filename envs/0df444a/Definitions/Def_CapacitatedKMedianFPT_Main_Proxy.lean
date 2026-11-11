-- Prove2me | Definitions.Def_CapacitatedKMedianFPT_Main_Proxy
-- name    : CapacitatedKMedianFPT_Main_Proxy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:14:27.594817+00:00
-- url     : https://prove2.me/theorems/877c8ce9-b75c-42d2-b8de-8c5bf763a141
-- title:
--   Facility groups, client types, proxy distances, count-matching assignments and the savings function
-- statement:
--   The objects of §3 (after the leader guess) and §4, for one branch of the enumeration: leaders $\ell_1,\dots,\ell_k$, radii $\tilde r_1,\dots,\tilde r_k\in\mathbb N$, a coloring $\chi:F\to[k]$, a permutation $\pi$ of $[k]$, and a nearest-leader choice $h(c)\in\arg\min_j d(c,\ell_j)$.
--
--   1. Groups (3.6): $F_i=\{f\in F:\chi(f)=\pi(i),\ d(f,\ell_i)\le\tilde r_i\}$; they are disjoint, and $f\in F_i$ forces $i=\pi^{-1}(\chi(f))$.
--   2. $\alpha_{c,i}=0$ if $d(\ell_{h(c)},\ell_i)=0$, and otherwise
--   $$\alpha_{c,i}=\varepsilon d(\ell_{h(c)},\ell_i)\left\lceil\frac{d(c,\ell_i)-d(c,\ell_{h(c)})}{\varepsilon d(\ell_{h(c)},\ell_i)}\right\rceil .$$
--   3. The type $T(c)=(h(c),\alpha_{c,1},\dots,\alpha_{c,k})$.
--   4. The proxy distance $\tilde d(c,f)=d(c,\ell_{h(c)})+\alpha_{c,i}+\tilde r_i$ for $f\in F_i$.
--   5. For an indexed optimum $(o^\star,\varphi^\star)$: $y_{T,i}$, the number of clients of type $T$ assigned to $o^\star_i$, and $Z=\sum_{c\in C}\tilde d(c,\varphi^\star(c))$.
--   6. $\varphi'$ is **count-matching** if it maps every client into $\bigcup_iF_i$ and sends exactly $y_{T,i}$ clients of type $T$ into $F_i$.
--   7. Weights $w(c,f)=\tilde d(c,f)-d(c,f)$. For quotas $q_{T,i}$, a **quota-constrained matching using $S$** is a partial assignment of clients to facilities of $S\cap\bigcup_iF_i$ giving every $f\in F_i$ at most $q_{T,i}$ clients of each type $T$; capacities are not imposed.
--   8. The **savings function** $v(S)$ is the maximum weight of a quota-constrained matching using $S$. The correct quotas are $\tilde y_{T,i}=\mu_\varepsilon(y_{T,i})$.
--
--   These objects are used by Lemmas 3–6 and Claims 2–3.
--
--   **Formalization Note** A type is a pair in $[k]\times\mathbb R^{k}$. $\tilde d(c,f)$ is defined for every $f$ using the index $\pi^{-1}(\chi(f))$; it agrees with the source on $\bigcup_iF_i$, the only place where it is read. The maximum in $v$ is a supremum of a finite nonempty set of reals (the empty matching is admissible).
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 9, Disjoint groups via color coding (3.6) and Client bucketing; p. 10, h(c), α_(c,i), types, proxy distance; p. 11, Z, upper quota y_(T,i), count-matching; p. 12, §4 weights, quota constraint, savings function v(S)

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Instance

set_option autoImplicit false

/-!
# Facility groups, client types, proxy distances, upper quotas and the savings function

Anand–Huang–Jaiswal–Kumar–Lee–Yadav, STOC 2027 submission #1646, §3 (p. 9–11) and §4 (p. 12).
-/

namespace CapacitatedKMedianFPT.Main

open scoped BigOperators

noncomputable section

open Classical

variable {P : Type} [Fintype P] [DecidableEq P]

/-- One branch of the enumeration of §3: leaders `ℓ_1, …, ℓ_k`, radii `r̃_1, …, r̃_k`, a coloring
`χ : F → [k]`, a permutation `π` of `[k]`, and the index `h(c)` of a nearest leader of each client
(ties broken by `h`). -/
structure Guess (I : Instance P) where
  ℓ : Fin I.k → P
  r : Fin I.k → ℕ
  χ : P → Fin I.k
  π : Equiv.Perm (Fin I.k)
  h : P → Fin I.k

/-- A client type `(h, α_1, …, α_k)` (p. 9). -/
abbrev ClientType (k : ℕ) := Fin k × (Fin k → ℝ)

namespace Guess

variable {I : Instance P} (G : Guess I)

/-- (3.6): `F_i = {f ∈ F : χ(f) = π(i), d(f, ℓ_i) ≤ r̃_i}`. -/
def group (i : Fin I.k) : Finset P :=
  I.F.filter (fun f => G.χ f = G.π i ∧ I.d f (G.ℓ i) ≤ G.r i)

/-- `⋃_i F_i`. -/
def groupUnion : Finset P := Finset.univ.biUnion G.group

/-- The index `π⁻¹(χ(f))`, which is the unique `i` with `f ∈ F_i` whenever `f ∈ ⋃_i F_i`. -/
def groupIndex (f : P) : Fin I.k := G.π.symm (G.χ f)

/-- `h(c)` is the index of a nearest leader: `h(c) ∈ argmin_j d(c, ℓ_j)` (p. 10). -/
def IsNearestLeader : Prop := ∀ c ∈ I.C, ∀ j, I.d c (G.ℓ (G.h c)) ≤ I.d c (G.ℓ j)

/-- `α_{c,i}` (p. 10): `0` if `d(ℓ_{h(c)}, ℓ_i) = 0`, otherwise
`ε d(ℓ_{h(c)}, ℓ_i) · ⌈(d(c, ℓ_i) − d(c, ℓ_{h(c)})) / (ε d(ℓ_{h(c)}, ℓ_i))⌉`. -/
def alpha (ε : ℝ) (c : P) (i : Fin I.k) : ℝ :=
  if I.d (G.ℓ (G.h c)) (G.ℓ i) = 0 then 0
  else ε * I.d (G.ℓ (G.h c)) (G.ℓ i) *
    ⌈(I.d c (G.ℓ i) - I.d c (G.ℓ (G.h c))) / (ε * I.d (G.ℓ (G.h c)) (G.ℓ i))⌉

/-- The type `T(c) = (h(c), α_{c,1}, …, α_{c,k})`. -/
def type (ε : ℝ) (c : P) : ClientType I.k := (G.h c, fun i => G.alpha ε c i)

/-- The proxy distance `d̃(c, f) = d(c, ℓ_{h(c)}) + α_{c,i} + r̃_i` for `f ∈ F_i` (p. 10). -/
def proxyDist (ε : ℝ) (c f : P) : ℝ :=
  I.d c (G.ℓ (G.h c)) + G.alpha ε c (G.groupIndex f) + G.r (G.groupIndex f)

/-- `y_{T,i}`: the number of clients of type `T` assigned to `o⋆_i` by `φ⋆` (p. 11). -/
def typeCount (ε : ℝ) (o : Fin I.k → P) (φ : P → P) (T : ClientType I.k) (i : Fin I.k) : ℕ :=
  (I.C.filter (fun c => G.type ε c = T ∧ φ c = o i)).card

/-- `Z = ∑_{c ∈ C} d̃(c, φ⋆(c))` (p. 11). -/
def proxyOpt (ε : ℝ) (φ : P → P) : ℝ := ∑ c ∈ I.C, G.proxyDist ε c (φ c)

/-- Count-matching (p. 11): `φ'` maps clients into `⋃_i F_i` and sends exactly `y_{T,i}` clients of
type `T` into `F_i`, for every type `T` and every `i`. -/
def IsCountMatching (ε : ℝ) (o : Fin I.k → P) (φ φ' : P → P) : Prop :=
  (∀ c ∈ I.C, φ' c ∈ G.groupUnion) ∧
    ∀ (T : ClientType I.k) (i : Fin I.k),
      (I.C.filter (fun c => G.type ε c = T ∧ φ' c ∈ G.group i)).card = G.typeCount ε o φ T i

/-- The edge weight `w(c, f) = d̃(c, f) − d(c, f)` (p. 12). -/
def weight (ε : ℝ) (c f : P) : ℝ := G.proxyDist ε c f - I.d c f

/-- A quota-constrained matching using `S` (p. 12): a partial assignment of clients to facilities
of `S ∩ ⋃_i F_i` such that every facility `f ∈ F_i` receives at most `q(T, i)` clients of each
type `T`. Capacities `U_f` are not imposed. -/
def IsQuotaMatching (ε : ℝ) (q : ClientType I.k → Fin I.k → ℕ) (S : Finset P)
    (γ : P → Option P) : Prop :=
  (∀ c f, γ c = some f → c ∈ I.C ∧ f ∈ S ∧ f ∈ G.groupUnion) ∧
    ∀ f ∈ S, ∀ T : ClientType I.k,
      (I.C.filter (fun c => γ c = some f ∧ G.type ε c = T)).card ≤ q T (G.groupIndex f)

/-- The weight `∑_{c matched} w(c, γ(c))` of a partial assignment. -/
def matchWeight (ε : ℝ) (γ : P → Option P) : ℝ :=
  ∑ c ∈ I.C, (match γ c with
    | some f => G.weight ε c f
    | none => 0)

/-- The savings function `v(S)` (p. 12): the maximum weight of a quota-constrained matching using
`S`. The maximum is over a finite nonempty set (the empty matching is admissible). -/
def savings (ε : ℝ) (q : ClientType I.k → Fin I.k → ℕ) (S : Finset P) : ℝ :=
  sSup {x : ℝ | ∃ γ : P → Option P, G.IsQuotaMatching ε q S γ ∧ x = G.matchWeight ε γ}

/-- The rounded quotas of the correct guess: `ỹ_{T,i} = μ_ε(y_{T,i})` (p. 11–12). -/
def roundedQuota (ε : ℝ) (o : Fin I.k → P) (φ : P → P) : ClientType I.k → Fin I.k → ℕ :=
  fun T i => geomRound ε (G.typeCount ε o φ T i)

end Guess

end

end CapacitatedKMedianFPT.Main


