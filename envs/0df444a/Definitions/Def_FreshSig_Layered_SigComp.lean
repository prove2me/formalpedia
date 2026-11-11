-- Prove2me | Definitions.Def_FreshSig_Layered_SigComp
-- name    : FreshSig_Layered_SigComp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:43:14.39718+00:00
-- url     : https://prove2.me/theorems/5ff045ca-3105-486b-9a0b-8596fc7ac293
-- title:
--   The layered scheme SigComp and the model of Section 3.1
-- statement:
--   An epoch signature of SigComp is $\hat\sigma=(i,m,\sigma,U,W,G)$ with party indices $U=(u_0,\dots,u_h)$, path values $W=(\rho_0,\dots,\rho_h)$ and proofs $G=(\gamma_0,\dots,\gamma_{h-1})$; its depth is $d-h$.
--
--   **Refresh** (common input $[n]$, $d$, $g$) at $P_i$: invoke the nonce routine, obtaining $\nu_i$; let $V_i^0$ have $\mathrm{leaf}(g,\nu_i)$ at position $i$ and $\bot$ elsewhere and $r_i^0=\mathrm{root}_0(V_i^0)$; for $\ell=1,\dots,d$ invoke the commitment routine with label $g$, depth $\ell$ and input $r_i^{\ell-1}$, obtaining $(V_i^\ell,r_i^\ell,\pi_i^\ell)$, $a_i^\ell=(V_i^\ell,\pi_i^\ell)$; output $R_i=(r_i^0,\dots,r_i^d)$, $A_i=(a_i^1,\dots,a_i^d)$. In the synchronous model the nonce routine is invoked in the common start round $\tau_0$, layer $\ell$ in round $\tau_0+t_N+(\ell-1)t_C$ (once the outputs it needs are there), and the output is produced in round $\tau_0+t_{ref}$, $t_{ref}=t_N+d\,t_C$.
--
--   **Signing:** reject unless $r_i^d$ is a root of depth $d$; $\rho_0=r_i^d$, $x=(\mathrm{LF},g,m,\rho_0)$, $\sigma\leftarrow\mathrm{Sign}_i(x)$; return $(i,m,\sigma,(i),(\rho_0),())$.
--
--   **Forwarding** $P_j\to P_k$ at depth $q$: reject failed parses and $q\notin[1,d]$; require $\mathrm{Verify}_j(i,m,\hat\sigma,R_j,q)=1$; take $v=v^q_{j,k}$, $\pi=\pi^q_{j,k}$ from $a^q_j$, require that $v$ is a root of depth $q-1$ and $\mathrm{OpenVerify}(r^q_j,k,v,\pi)=1$, else return $\bot$; append $u_{h+1}=k$, $\rho_{h+1}=v$, $\gamma_h=\pi$.
--
--   **Verification** at $P_j$: accept exactly when (i) $\hat\sigma$ parses with $\iota=i$, $\mu=m$, all fields of the specified types, $\rho_a$ a root of depth $d-a$, $u_0=i$, $u_h=j$, $0\le h\le d$, $q=d-h$; (ii) $\mathrm{Verify}(i,(\mathrm{LF},g,m,\rho_0),\sigma)=1$; (iii) $\mathrm{OpenVerify}(\rho_a,u_{a+1},\rho_{a+1},\gamma_a)=1$ for all $a<h$; (iv) $\rho_h=r_j^q$.
--
--   A forwarding record $(r^\ell,a^\ell)$ is **well formed** if $r^\ell$ is a root of depth $\ell$, every entry of $V^\ell$ is a root of depth $\ell-1$ or $\bot$, and the proofs open the non-$\bot$ entries; lists are well formed if every $r^\ell$ is a root of depth $\ell$ and every record is well formed.
--
--   **The model of Section 3.1** (`Sec31`): executions obeying the symbolic rules, in which every party runs refresh as above and verifies only against its own refresh output while it is correct, and the nonce routine (Definition A.5, freshness at every correct party) and the commitment routine (Definition A.9) meet their guarantees with durations $t_N$ and $t_C$. The adversary may, before $\tau_0$ (preparation phase) and after it, corrupt any number of parties adaptively and call every signing interface on anything it can compute. The routine **delivered from $P_k$ to $P_j$** in layer $\ell$ iff $v^\ell_{j,k}=v^\ell_k$.
--
--   **Formalization Note** `SigComp.parse`, `mk`, `statement`, `sign`, `signStatement`, `forward`, `verify`, `info`, `WFRecord`, `WellFormedR`, `WellFormedLists`, `ValidEntry`; `sigComp n : EpochScheme`. Refresh is described by `FollowsRefresh` (each step at its round, with its input computed from the outputs `Obtained` before it, taken once, and taken whenever its inputs are available) and the lists by `listsR`, `listsA`. Party indices are $0,\dots,n-1$; `LF` is the public constant `cst "LF"`.
-- source:
--   Lenzen, Loss, Shi, Fresh Signatures without Fresh Keys, STOC 2027 submission (manuscript sha256 ac05cb97…), p. 13, §3.1; pp. 13–14, §3.2 (box "The scheme SigComp" and the paragraph after it); p. 55 (reserved tag LF)

import Mathlib
import Definitions.Def_FreshSig_Layered_Term
import Definitions.Def_FreshSig_Layered_Execution
import Definitions.Def_FreshSig_Layered_EpochScheme

/-!
# The layered scheme SigComp and the model of Section 3.1

Lenzen, Loss, Shi, *Fresh Signatures without Fresh Keys*, STOC 2027 submission,
§3.1 (requirements on the model, p. 13) and §3.2 (the box "The scheme SigComp" and the paragraph
after it, pp. 13–14).

An epoch signature is the tuple `σ̂ = (i, m, σ, U, W, G)` with `U = (u₀, …, u_h)` party
identities, `W = (ρ₀, …, ρ_h)` path values and `G = (γ₀, …, γ_{h-1})` proofs; its depth is
`d - h`. The local algorithms take the party count `n`, the maximum depth `d` and the label `g`.
-/

namespace FreshSig.Layered

namespace SigComp

open Classical

/-- Parse a list of party identities. -/
def parsePids : List Term → Option (List ℕ)
  | [] => some []
  | Term.pid u :: ts => (parsePids ts).map (u :: ·)
  | _ :: _ => none

/-- Parse `σ̂ = (ι, μ, σ, U, W, G)`; `none` for a failed parse. -/
def parse : Term → Option (ℕ × Term × Term × List ℕ × List Term × List Term)
  | Term.tup [Term.pid ι, μ, σ, Term.tup Us, Term.tup W, Term.tup G] =>
      (parsePids Us).map (fun U => (ι, μ, σ, U, W, G))
  | _ => none

/-- The epoch signature term `(i, m, σ, U, W, G)`. -/
def mk (i : ℕ) (m σ : Term) (U : List ℕ) (W G : List Term) : Term :=
  Term.tup [Term.pid i, m, σ, Term.tup (U.map Term.pid), Term.tup W, Term.tup G]

/-- The signed statement `(LF, g, m, ρ₀)`. -/
def statement (g m ρ₀ : Term) : Term := Term.tup [LF, g, m, ρ₀]

/-- Verification `GSig.Verifyⱼ(i, m, σ̂, Rⱼ, q) = 1` (step 4 of the box): parse
`σ̂ = (ι, μ, σ, U, W, G)` and accept exactly when (i) `ι = i`, `μ = m`, all fields have the
specified types, `ρ_a` is a root of depth `d - a`, `u₀ = i`, `u_h = j`, `0 ≤ h ≤ d` and
`q = d - h`; (ii) `Verify(i, (LF, g, m, ρ₀), σ) = 1`; (iii) `OpenVerify(ρ_a, u_{a+1}, ρ_{a+1}, γ_a) = 1`
for every `a < h`; (iv) `ρ_h = r_j^q`. -/
def verify (n d : ℕ) (g : Term) (j i : ℕ) (m σhat : Term) (R : List Term) (q : ℕ) : Prop :=
  ∃ (σ : Term) (U : List ℕ) (W G : List Term) (h : ℕ),
    parse σhat = some (i, m, σ, U, W, G) ∧
    U.length = h + 1 ∧ W.length = h + 1 ∧ G.length = h ∧ (∀ u ∈ U, u < n) ∧
    (∀ (a : ℕ) (ρ : Term), W[a]? = some ρ → IsRoot n (d - a) ρ) ∧
    U[0]? = some i ∧ U[h]? = some j ∧ h ≤ d ∧ q = d - h ∧
    (∃ ρ₀, W[0]? = some ρ₀ ∧ SigVerify i (statement g m ρ₀) σ) ∧
    (∀ a < h, ∃ (u : ℕ) (ρ ρ' γ : Term), U[a + 1]? = some u ∧ W[a]? = some ρ ∧
      W[a + 1]? = some ρ' ∧ G[a]? = some γ ∧ OpenVerify ρ u (some ρ') (some γ)) ∧
    (∃ ρh, W[h]? = some ρh ∧ R[q]? = some ρh)

/-- The statement that signing submits to `Signᵢ`: `(LF, g, m, r_i^d)`, provided `r_i^d` is a root
of depth `d` (otherwise signing rejects). -/
noncomputable def signStatement (n d : ℕ) (g : Term) (_i : ℕ) (m : Term) (R : List Term) :
    Option Term :=
  match R[d]? with
  | some r => if IsRoot n d r then some (statement g m r) else none
  | none => none

/-- Signing (step 2 of the box): reject unless `r_i^d` is a root of depth `d`; set `ρ₀ = r_i^d`,
`x = (LF, g, m, ρ₀)`, `σ ← Signᵢ(x)`, and return `(i, m, σ, (i), (ρ₀), ())`. -/
noncomputable def sign (n d : ℕ) (g : Term) (i : ℕ) (m : Term) (R : List Term) : Option Term :=
  match R[d]? with
  | some r => if IsRoot n d r then some (mk i m (Term.sig i (statement g m r)) [i] [r] []) else none
  | none => none

/-- Forwarding `GSig.Forward_{j→k}(i, m, σ̂, Rⱼ, Aⱼ, q)` (step 3 of the box): reject failed parses
and `q ∉ [1, d]`; require `Verifyⱼ(i, m, σ̂, Rⱼ, q) = 1`; let `v = v^q_{j,k}` and `π = π^q_{j,k}`
from `a^q_j` and require that `v` is a root of depth `q - 1` and `OpenVerify(r_j^q, k, v, π) = 1`;
otherwise return `⊥`. Append `u_{h+1} = k`, `ρ_{h+1} = v` and `γ_h = π`. -/
noncomputable def forward (n d : ℕ) (g : Term) (j k i : ℕ) (m σhat : Term) (R : List Term)
    (A : List FwdRecord) (q : ℕ) : Option Term :=
  match parse σhat with
  | none => none
  | some (ι, μ, σ, U, W, G) =>
    if 1 ≤ q ∧ q ≤ d ∧ verify n d g j i m σhat R q then
      match A[q - 1]?, R[q]? with
      | some a, some r =>
        match a.1[k]?, a.2[k]? with
        | some (some v), some (some π) =>
          if IsRoot n (q - 1) v ∧ OpenVerify r k (some v) (some π) then
            some (mk ι μ σ (U ++ [k]) (W ++ [v]) (G ++ [π]))
          else none
        | _, _ => none
      | _, _ => none
    else none

/-- Origin, message, holder `u_h` and depth `d - h` of a parsed signature. -/
def info (d : ℕ) (σhat : Term) : Option SigInfo :=
  match parse σhat with
  | some (ι, μ, _, U, _, G) => (U.getLast?).map (fun k => ⟨ι, μ, k, d - G.length⟩)
  | none => none

/-- A well-formed forwarding record `(rℓ, aℓ)` (p. 14): `rℓ` is a root of depth `ℓ`, `Vℓ` has `n`
entries each a root of depth `ℓ - 1` or `⊥`, and the proofs open the non-`⊥` entries. -/
def WFRecord (n ℓ : ℕ) (r : Term) (a : FwdRecord) : Prop :=
  IsRoot n ℓ r ∧ a.1.length = n ∧
  (∀ (k : ℕ) (v : Term), a.1[k]? = some (some v) → IsRoot n (ℓ - 1) v) ∧
  (∀ (k : ℕ) (v : Term), a.1[k]? = some (some v) →
    ∃ π, a.2[k]? = some (some π) ∧ OpenVerify r k (some v) (some π))

/-- A well-formed reference list `R = (r⁰, …, r^d)`: every `rℓ` is a root of depth `ℓ`. -/
def WellFormedR (n d : ℕ) (R : List Term) : Prop :=
  R.length = d + 1 ∧ ∀ (ℓ : ℕ) (r : Term), R[ℓ]? = some r → IsRoot n ℓ r

/-- Well-formed lists `(R, A)`: `R` well formed, `A = (a¹, …, a^d)`, and every record `(rℓ, aℓ)`,
`1 ≤ ℓ ≤ d`, well formed. -/
def WellFormedLists (n d : ℕ) (R : List Term) (A : List FwdRecord) : Prop :=
  WellFormedR n d R ∧ A.length = d ∧
  ∀ (ℓ : ℕ) (r : Term) (a : FwdRecord), 1 ≤ ℓ → R[ℓ]? = some r → A[ℓ - 1]? = some a →
    WFRecord n ℓ r a

/-- Valid forwarding information for recipient `k` against `r^q`: `v` is a root of depth `q - 1`
and `OpenVerify(r^q, k, v, π) = 1`. -/
def ValidEntry (n q : ℕ) (r : Term) (k : ℕ) (v π : Term) : Prop :=
  IsRoot n (q - 1) v ∧ OpenVerify r k (some v) (some π)

end SigComp

/-- The layered scheme SigComp for the party set `[n]`, as an epoch signature scheme. -/
noncomputable def sigComp (n : ℕ) : EpochScheme where
  sign := SigComp.sign n
  signStatement := SigComp.signStatement n
  forward := SigComp.forward n
  verify := SigComp.verify n
  info := SigComp.info
  wellFormedR := SigComp.WellFormedR n
  wellFormedLists := SigComp.WellFormedLists n
  validRecord := SigComp.WFRecord n
  validEntry := SigComp.ValidEntry n

namespace SigComp

/-- The output `(Vℓ, rℓ, πℓ)` of one layer of refresh. -/
structure LayerOut where
  V : List (Option Term)
  ρ : Term
  π : List (Option Term)

/-- `V⁰ᵢ`: the entry `leaf(g, νᵢ)` at position `i` and `⊥` elsewhere. -/
def baseVec (n : ℕ) (g : Term) (i : ℕ) (ν : Term) : List (Option Term) :=
  (List.range n).map (fun k => if k = i then some (leafOf g ν) else none)

/-- The reference values of party `i` in terms of its nonce `ν` and its layer outputs `L`:
`r⁰ = root(V⁰)` (computed locally, depth 0) and `rℓ` the root output by layer `ℓ`. -/
def refVal (n : ℕ) (g : Term) (i : ℕ) (ν : Term) (L : ℕ → LayerOut) : ℕ → Term
  | 0 => Term.root 0 (baseVec n g i ν)
  | ℓ + 1 => (L (ℓ + 1)).ρ

/-- The output lists `Rᵢ = (r⁰ᵢ, …, r^dᵢ)` and `Aᵢ = (a¹ᵢ, …, a^dᵢ)`, `aℓᵢ = (Vℓᵢ, πℓᵢ)`. -/
def listsR (n : ℕ) (g : Term) (i : ℕ) (ν : Term) (L : ℕ → LayerOut) (d : ℕ) : List Term :=
  (List.range (d + 1)).map (refVal n g i ν L)

/-- See `listsR`. -/
def listsA (L : ℕ → LayerOut) (d : ℕ) : List FwdRecord :=
  (List.range d).map (fun ℓ => ((L (ℓ + 1)).V, (L (ℓ + 1)).π))

/-- `Obtained tr τ₀ n g i ν L ℓ p`: before position `p`, party `i` has, in the execution phase,
invoked the nonce routine and obtained `ν`, and for each layer `1, …, ℓ` in turn invoked the
commitment routine with label `g`, that depth and input `r^{ℓ'-1}` and obtained `L ℓ'`. -/
def Obtained (tr : Execution) (τ₀ n : ℕ) (g : Term) (i : ℕ) (ν : Term) (L : ℕ → LayerOut) :
    ℕ → Pos → Prop
  | 0, p => ∃ pI pO : Pos, PosLE (τ₀, 0) pI ∧ PosLT pI pO ∧ PosLT pO p ∧
      evAt tr pI = some (Event.nonceInv i g) ∧ evAt tr pO = some (Event.nonceOut i g (some ν))
  | ℓ + 1, p => ∃ pI pO : Pos, PosLT pI pO ∧ PosLT pO p ∧
      evAt tr pI = some (Event.commitInv i g (ℓ + 1) (refVal n g i ν L ℓ)) ∧
      evAt tr pO = some (Event.commitOut i g (ℓ + 1) (L (ℓ + 1)).V (L (ℓ + 1)).ρ (L (ℓ + 1)).π) ∧
      Obtained tr τ₀ n g i ν L ℓ pI

/-- The round in which layer `ℓ ≥ 1` is invoked: `τ₀ + tN + (ℓ - 1) tC`. -/
def layerRound (τ₀ tN tC ℓ : ℕ) : ℕ := τ₀ + tN + (ℓ - 1) * tC

/-- The refresh duration `tref = tN + d·tC` (p. 13). -/
def tref (tN tC d : ℕ) : ℕ := tN + d * tC

/-- Party `i` runs refresh of SigComp (step 1 of the box) with common input `[n]`, `d`, `g`, in
lockstep from the common start `τ₀`, as long as it is correct: it invokes the nonce routine in
round `τ₀`; layer `ℓ` (`1 ≤ ℓ ≤ d`) in round `τ₀ + tN + (ℓ - 1) tC` with input `r^{ℓ-1}`, once the
outputs it needs are available; and it outputs `(Rᵢ, Aᵢ)` in round `τ₀ + tN + d tC`, once all
outputs are available. Each step is taken once and only as prescribed. -/
structure FollowsRefresh (n d : ℕ) (g : Term) (τ₀ tN tC : ℕ) (tr : Execution) (i : ℕ) : Prop where
  nonce_round : ∀ p : Pos, CorrectAt tr τ₀ i p → evAt tr p = some (Event.nonceInv i g) → p.1 = τ₀
  nonce_unique : ∀ p p' : Pos, CorrectAt tr τ₀ i p → CorrectAt tr τ₀ i p' →
    evAt tr p = some (Event.nonceInv i g) → evAt tr p' = some (Event.nonceInv i g) → p = p'
  nonce_exists : CorrectThrough tr τ₀ i τ₀ →
    ∃ p : Pos, p.1 = τ₀ ∧ evAt tr p = some (Event.nonceInv i g)
  layer_step : ∀ (p : Pos) (ℓ : ℕ) (v : Term), CorrectAt tr τ₀ i p →
    evAt tr p = some (Event.commitInv i g ℓ v) →
    1 ≤ ℓ ∧ ℓ ≤ d ∧ p.1 = layerRound τ₀ tN tC ℓ ∧
    ∃ (ν : Term) (L : ℕ → LayerOut), Obtained tr τ₀ n g i ν L (ℓ - 1) p ∧
      v = refVal n g i ν L (ℓ - 1)
  layer_unique : ∀ (p p' : Pos) (ℓ : ℕ) (v v' : Term), CorrectAt tr τ₀ i p → CorrectAt tr τ₀ i p' →
    evAt tr p = some (Event.commitInv i g ℓ v) → evAt tr p' = some (Event.commitInv i g ℓ v') →
    p = p'
  layer_exists : ∀ (ℓ : ℕ) (ν : Term) (L : ℕ → LayerOut), 1 ≤ ℓ → ℓ ≤ d →
    CorrectThrough tr τ₀ i (layerRound τ₀ tN tC ℓ) →
    Obtained tr τ₀ n g i ν L (ℓ - 1) (layerRound τ₀ tN tC ℓ + 1, 0) →
    ∃ p : Pos, p.1 = layerRound τ₀ tN tC ℓ ∧ Obtained tr τ₀ n g i ν L (ℓ - 1) p ∧
      evAt tr p = some (Event.commitInv i g ℓ (refVal n g i ν L (ℓ - 1)))
  out_step : ∀ (p : Pos) (R : List Term) (A : List FwdRecord), CorrectAt tr τ₀ i p →
    evAt tr p = some (Event.refreshOut i g R A) →
    p.1 = τ₀ + tref tN tC d ∧ ∃ (ν : Term) (L : ℕ → LayerOut), Obtained tr τ₀ n g i ν L d p ∧
      R = listsR n g i ν L d ∧ A = listsA L d
  out_exists : ∀ (ν : Term) (L : ℕ → LayerOut), CorrectThrough tr τ₀ i (τ₀ + tref tN tC d) →
    Obtained tr τ₀ n g i ν L d (τ₀ + tref tN tC d + 1, 0) →
    ∃ p : Pos, p.1 = τ₀ + tref tN tC d ∧ Obtained tr τ₀ n g i ν L d p ∧
      evAt tr p = some (Event.refreshOut i g (listsR n g i ν L d) (listsA L d))

/-- A model `M+` satisfying Section 3.1, for SigComp with party set `[n]`, maximum depth `d`,
label `g`, common start round `τ₀`, nonce routine of duration `tN` and commitment routine of
duration `tC`: the executions obeying the symbolic rules in which every party, as long as it is
correct, runs refresh and verification as prescribed, and the nonce and commitment routines
satisfy Definitions A.5 (freshness at every correct party) and A.9. The adversary is otherwise
unrestricted: before `τ₀` (the preparation phase) and after it, it may corrupt any number of
parties adaptively and call every signing interface on anything it can compute. -/
structure Sec31 (n d : ℕ) (g : Term) (τ₀ tN tC : ℕ) (tr : Execution) : Prop where
  admissible : Admissible n tr
  refresh : ∀ i < n, FollowsRefresh n d g τ₀ tN tC tr i
  verification : (sigComp n).FollowsVerification n d g τ₀ tr
  nonce : NonceRoutine n g τ₀ tN tr
  commitment : CommitRoutine n g τ₀ tC tr

/-- The commitment routine delivered from `P_k` to `P_j` in layer `ℓ` (p. 63): `v_{j,k} = v_k`,
where `v_k` is the input of the correct `P_k` and `V_j` the output of the correct `P_j`. -/
def Delivered (tr : Execution) (τ₀ : ℕ) (g : Term) (ℓ k j : ℕ) : Prop :=
  ∃ (pk pj : Pos) (vk : Term) (V : List (Option Term)) (ρ : Term) (π : List (Option Term)),
    CorrectAt tr τ₀ k pk ∧ evAt tr pk = some (Event.commitInv k g ℓ vk) ∧
    CorrectAt tr τ₀ j pj ∧ evAt tr pj = some (Event.commitOut j g ℓ V ρ π) ∧
    V[k]? = some (some vk)

end SigComp

end FreshSig.Layered


