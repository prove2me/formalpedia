-- Prove2me | Definitions.Def_FreshSig_Layered_EpochScheme
-- name    : FreshSig_Layered_EpochScheme
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:42:30.456772+00:00
-- url     : https://prove2.me/theorems/ecc9cae4-390c-46c2-9e72-1ba9ada3d7a1
-- title:
--   Epoch signature schemes: interface (Definition A.1), $X_j\sim_q X_k$, correctness (Definition A.2), epoch unforgeability (Definition A.3), realisation (Definition A.4)
-- statement:
--   An **epoch signature scheme** (Definition A.1) for parties $[n]$ consists of a distributed refresh protocol with local outputs $R_i=(r_i^0,\dots,r_i^d)$, $A_i=(a_i^1,\dots,a_i^d)$, $a_i^\ell=(V_i^\ell,\pi_i^\ell)$, and local algorithms with common inputs the maximum depth $d$ and the label $g$: signing $\mathrm{Sign}_i(m,R_i)$, which submits one statement to $\mathrm{Sign}_i$; forwarding $\mathrm{Forward}_{j\to k}(i,m,\hat\sigma,R_j,A_j,q)$; verification $\mathrm{Verify}_j(i,m,\hat\sigma,R_j,q)\in\{0,1\}$; together with deterministic tests for well-formed lists and valid forwarding records, and the origin, message, holder and depth that a signature identifies. $X_j\sim_q X_k$ holds iff $q>0$, the record $(r_j^q,a_j^q)$ is valid and its entry for $k$ is $v^q_{j,k}=r_k^{q-1}$ with a valid proof.
--
--   **Correctness (Definition A.2):** (1) for every well-formed $R_i$, signing returns a signature of depth $d$ with $\mathrm{Verify}_i(i,m,\mathrm{Sign}_i(m,R_i),R_i,d)=1$; (2) if $1\le q\le d$, $X_j\sim_q X_k$ and $\mathrm{Verify}_j(i,m,\hat\sigma,R_j,q)=1$, then forwarding returns $\hat\sigma'\ne\bot$ with origin $i$, message $m$, holder $k$, depth $q-1$ and $\mathrm{Verify}_k(i,m,\hat\sigma',R_k,q-1)=1$, for every candidate; (3) acceptance implies that the holder is the verifier and $0\le q=\mathrm{depth}(\hat\sigma)\le d$, and forwarding rejects invalid signatures, incorrect depths, depth zero and missing or locally invalid forwarding information; (4) a correct party that completes refresh obtains well-formed lists.
--
--   A **signing call for $(i,m)$** with label $g$ is a call of $\mathrm{Sign}_i$ on a statement that $\mathrm{Sign}_i(m,R)$ submits for some admissible $R$.
--
--   **Epoch unforgeability (Definition A.3)** at a verifier $P_j$, start round $\tau_0$: whenever $P_j$, correct up to that event, accepts $\hat\sigma$ as a signature of origin $i$ on $m$ in the epoch with label $g$, then $\hat\sigma$ has an ideal signature as a structural subterm whose first issue is a signing call for $(i,m)$ with label $g$, at or after round $\tau_0$ and no later than the acceptance.
--
--   **Realisation (Definition A.4)** in a class $M$ of executions, with maximum depth $d$ and refresh duration $t_{ref}$: correctness items (1)–(3); and in every execution of $M$: every party correct through round $\tau_0+t_{ref}$ completes refresh within $t_{ref}$ rounds; item (4); between parties correct through refresh, forwarding an accepted candidate at depth $q$ succeeds only when $X_j\sim_q X_k$; epoch unforgeability at every verifier.
--
--   **Formalization Note** `EpochScheme` bundles the local algorithms and tests (`sign`, `signStatement`, `forward`, `verify` as a proposition, `info`, `wellFormedR`, `wellFormedLists`, `validRecord`, `validEntry`); `R[ℓ]` is $r^\ell$ and `A[ℓ - 1]` is $a^\ell$. `Compat`, `CorrectA2` (items 1–3, for all $d$, with $i,j,k<n$), `RefreshCorrectIn` (item 4 in one execution), `IsSigningCallFor`, `EpochUnforgeableAt`, `FollowsVerification` (a correct verifier accepts only what `verify` accepts against its own refresh output) and `Realised` follow the text. Refresh, a distributed protocol, enters through the class `M`.
-- source:
--   Lenzen, Loss, Shi, Fresh Signatures without Fresh Keys, STOC 2027 submission (manuscript sha256 ac05cb97…), pp. 55–57, Appendix A.2 (Definitions A.1, A.2, A.3); p. 60, Definition A.4

import Mathlib
import Definitions.Def_FreshSig_Layered_Term
import Definitions.Def_FreshSig_Layered_Execution

/-!
# Epoch signature schemes: interface, correctness, epoch unforgeability, realisation

Lenzen, Loss, Shi, *Fresh Signatures without Fresh Keys*, STOC 2027 submission,
Appendix A.2 (Definitions A.1, A.2, A.3; pp. 55–57) and A.4 (Definition A.4; p. 60).

The local algorithms of a scheme with party set `[n]` take the maximum depth `d` and the epoch
label `g` (common inputs) explicitly. Local lists have the format of p. 56: `R = (r⁰, …, r^d)` and
`A = (a¹, …, a^d)` with `aℓ = (Vℓ, πℓ)`; a list element `R[ℓ]` is `rℓ` and `A[ℓ - 1]` is `aℓ`.
Verification returns `1` exactly when the proposition `verify …` holds.
-/

namespace FreshSig.Layered

/-- What a well-formed signature identifies (p. 56): origin, message, current holder, depth. -/
structure SigInfo where
  origin : ℕ
  msg : Term
  holder : ℕ
  depth : ℕ

/-- Definition A.1: the local algorithms of an epoch signature scheme, together with its
deterministic tests for well-formed lists and valid forwarding records (p. 56). Refresh is a
distributed protocol; its prescribed behaviour is part of the execution model of each scheme.
* `sign d g i m R` — `GSig.Signᵢ(m, Rᵢ)`, `none` = `⊥`;
* `signStatement d g i m R` — the statement `GSig.Signᵢ(m, R)` submits to `Signᵢ`;
* `forward d g j k i m σ R A q` — `GSig.Forward_{j→k}(i, m, σ̂, Rⱼ, Aⱼ, q)`;
* `verify d g j i m σ R q` — `GSig.Verifyⱼ(i, m, σ̂, Rⱼ, q) = 1`;
* `info d σ` — origin, message, holder and depth of a well-formed signature;
* `wellFormedR d R`, `wellFormedLists d R A` — the tests for well-formed lists;
* `validRecord q r a` — the test that `(r^q, a^q)` is a valid forwarding record;
* `validEntry q r k v π` — the test that `v` with proof `π` is valid forwarding information
  for recipient `k` against `r^q`. -/
structure EpochScheme where
  sign : ℕ → Term → ℕ → Term → List Term → Option Term
  signStatement : ℕ → Term → ℕ → Term → List Term → Option Term
  forward : ℕ → Term → ℕ → ℕ → ℕ → Term → Term → List Term → List FwdRecord → ℕ → Option Term
  verify : ℕ → Term → ℕ → ℕ → Term → Term → List Term → ℕ → Prop
  info : ℕ → Term → Option SigInfo
  wellFormedR : ℕ → List Term → Prop
  wellFormedLists : ℕ → List Term → List FwdRecord → Prop
  validRecord : ℕ → Term → FwdRecord → Prop
  validEntry : ℕ → Term → ℕ → Term → Term → Prop

namespace EpochScheme

variable (S : EpochScheme)

/-- `Xⱼ ∼_q X_k` (p. 56): `q > 0`, the record `(r_j^q, a_j^q)` is valid, and its entry for `k` is
`v^q_{j,k} = r_k^{q-1}` together with a valid proof. -/
def Compat (Rj : List Term) (Aj : List FwdRecord) (q k : ℕ) (Rk : List Term) : Prop :=
  0 < q ∧ ∃ (r : Term) (a : FwdRecord) (v π : Term),
    Rj[q]? = some r ∧ Aj[q - 1]? = some a ∧ S.validRecord q r a ∧
    a.1[k]? = some (some v) ∧ a.2[k]? = some (some π) ∧ Rk[q - 1]? = some v ∧
    S.validEntry q r k v π

/-- Definition A.2, item 1 (local correctness), for parties `i ∈ [n]`. -/
def LocalCorrectness (n : ℕ) : Prop :=
  ∀ (d : ℕ) (g : Term) (i : ℕ) (m : Term) (R : List Term), i < n → S.wellFormedR d R →
    ∃ σ, S.sign d g i m R = some σ ∧ (S.info d σ).map SigInfo.depth = some d ∧
      S.verify d g i i m σ R d

/-- Definition A.2, item 2 (forwardability), for every candidate, including ones built by
faulty parties, and every pair of lists with `Xⱼ ∼_q X_k`. -/
def Forwardability (n : ℕ) : Prop :=
  ∀ (d : ℕ) (g : Term) (q i j k : ℕ) (m σ : Term) (Rj : List Term) (Aj : List FwdRecord)
    (Rk : List Term), j < n → k < n → 1 ≤ q → q ≤ d → S.Compat Rj Aj q k Rk →
    S.verify d g j i m σ Rj q →
    ∃ σ', S.forward d g j k i m σ Rj Aj q = some σ' ∧
      S.info d σ' = some ⟨i, m, k, q - 1⟩ ∧ S.verify d g k i m σ' Rk (q - 1)

/-- Definition A.2, item 3 (rejection): acceptance implies that the holder is the verifier and
`0 ≤ q = depth(σ̂) ≤ d`; forwarding rejects invalid signatures, incorrect depths, depth zero, and
missing or locally invalid forwarding information. -/
def Rejection (n : ℕ) : Prop :=
  (∀ (d : ℕ) (g : Term) (j i : ℕ) (m σ : Term) (R : List Term) (q : ℕ),
      S.verify d g j i m σ R q → (S.info d σ).map SigInfo.holder = some j ∧
        (S.info d σ).map SigInfo.depth = some q ∧ q ≤ d) ∧
  (∀ (d : ℕ) (g : Term) (j k i : ℕ) (m σ : Term) (R : List Term) (A : List FwdRecord) (q : ℕ),
      j < n → S.forward d g j k i m σ R A q ≠ none →
      S.verify d g j i m σ R q ∧ 1 ≤ q ∧ q ≤ d ∧
      ∃ (r : Term) (a : FwdRecord) (v π : Term), R[q]? = some r ∧ A[q - 1]? = some a ∧
        a.1[k]? = some (some v) ∧ a.2[k]? = some (some π) ∧ S.validEntry q r k v π)

/-- Definition A.2, items 1–3 (the algebraic correctness of the local algorithms, for every
maximum depth, message and choice of lists). Item 4 is `RefreshCorrectIn`. -/
def CorrectA2 (n : ℕ) : Prop :=
  S.LocalCorrectness n ∧ S.Forwardability n ∧ S.Rejection n

/-- Definition A.2, item 4, in one execution: a correct party that completes refresh obtains
well-formed local lists. -/
def RefreshCorrectIn (n d : ℕ) (g : Term) (τ₀ : ℕ) (tr : Execution) : Prop :=
  ∀ i < n, ∀ (p : Pos) (R : List Term) (A : List FwdRecord), CorrectAt tr τ₀ i p →
    evAt tr p = some (Event.refreshOut i g R A) → S.wellFormedLists d R A

/-- A signing call for `(i, m)` with label `g` (p. 57): a call to `Signᵢ` on a statement that
`GSig.Signᵢ(m, R)` submits for some admissible reference list `R`. -/
def IsSigningCallFor (d : ℕ) (g : Term) (i : ℕ) (m : Term) (e : Option Event) : Prop :=
  ∃ (x : Term) (R : List Term), e = some (Event.signCall i x) ∧
    S.signStatement d g i m R = some x

/-- Definition A.3 (epoch unforgeability) at the verifier `j`, for the epoch with label `g` whose
designated start is round `τ₀` (so `hⱼ` is the prefix before round `τ₀`): whenever `j`, correct up
to that event, accepts `σ̂` as a signature of origin `i` on `m`, `σ̂` has an ideal signature as a
structural subterm whose first issue is a signing call for `(i, m)` with label `g`, after `hⱼ`
and no later than the acceptance event. -/
def EpochUnforgeableAt (d : ℕ) (g : Term) (τ₀ : ℕ) (tr : Execution) (j : ℕ) : Prop :=
  ∀ (p : Pos) (i : ℕ) (m σ : Term) (q : ℕ), CorrectAt tr τ₀ j p →
    evAt tr p = some (Event.accept j g i m σ q) →
    ∃ x : Term, Occurs (Term.sig i x) σ ∧ ∃ e : Pos, FirstIssue tr (Term.sig i x) e ∧
      PosLE (τ₀, 0) e ∧ PosLE e p ∧ S.IsSigningCallFor d g i m (evAt tr e)

/-- A correct verifier accepts only what its verification algorithm accepts, against the list of
its own refresh of this epoch. -/
def FollowsVerification (n d : ℕ) (g : Term) (τ₀ : ℕ) (tr : Execution) : Prop :=
  ∀ j < n, ∀ (p : Pos) (i : ℕ) (m σ : Term) (q : ℕ), CorrectAt tr τ₀ j p →
    evAt tr p = some (Event.accept j g i m σ q) →
    ∃ (p' : Pos) (R : List Term) (A : List FwdRecord), PosLT p' p ∧ CorrectAt tr τ₀ j p' ∧
      evAt tr p' = some (Event.refreshOut j g R A) ∧ S.verify d g j i m σ R q

/-- Definition A.4 (realisation): the scheme is realised in the model `M` (the class of its
executions against admissible adversaries with precorruptions in which the correct parties invoke
refresh as prescribed for the epoch with label `g`, starting in round `τ₀`) with maximum depth `d`
and refresh duration `tref`:
1. every correct party completes refresh within `tref` rounds;
2. the scheme is correct (Definition A.2, items 1–3, and item 4 in every execution);
3. between correct parties, forwarding an accepted candidate at depth `q` succeeds only when
   `Xⱼ ∼_q X_k`;
4. epoch unforgeability at every correct verifier. -/
def Realised (n : ℕ) (M : Execution → Prop) (d : ℕ) (g : Term) (τ₀ tref : ℕ) : Prop :=
  S.CorrectA2 n ∧
  ∀ tr : Execution, M tr →
    (∀ i < n, CorrectThrough tr τ₀ i (τ₀ + tref) →
      ∃ (p : Pos) (R : List Term) (A : List FwdRecord), τ₀ ≤ p.1 ∧ p.1 ≤ τ₀ + tref ∧
        evAt tr p = some (Event.refreshOut i g R A)) ∧
    S.RefreshCorrectIn n d g τ₀ tr ∧
    (∀ j < n, ∀ k < n, CorrectThrough tr τ₀ j (τ₀ + tref) → CorrectThrough tr τ₀ k (τ₀ + tref) →
      ∀ (pj pk : Pos) (Rj Rk : List Term) (Aj Ak : List FwdRecord),
        CorrectAt tr τ₀ j pj → evAt tr pj = some (Event.refreshOut j g Rj Aj) →
        CorrectAt tr τ₀ k pk → evAt tr pk = some (Event.refreshOut k g Rk Ak) →
        ∀ (q i : ℕ) (m σ : Term), S.verify d g j i m σ Rj q →
          S.forward d g j k i m σ Rj Aj q ≠ none → S.Compat Rj Aj q k Rk) ∧
    (∀ j < n, S.EpochUnforgeableAt d g τ₀ tr j)

end EpochScheme

end FreshSig.Layered


