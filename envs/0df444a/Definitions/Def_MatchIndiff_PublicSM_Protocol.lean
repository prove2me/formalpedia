-- Prove2me | Definitions.Def_MatchIndiff_PublicSM_Protocol
-- name    : MatchIndiff_PublicSM_Protocol
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:25:33.034299+00:00
-- url     : https://prove2.me/theorems/185923be-41e0-4084-8ba9-8a132805a547
-- title:
--   Board joint verification protocols, completeness, soundness and the cost ⌈log₂|C|⌉; IJVC/EJVC bounds at a public input (§2)
-- statement:
--   **Joint verification (p. 6).** Fix a public input $\xi$. Report holders $v\in V$ (in public-priority school choice: the students, $V=N$) have report sets $T_v$; a *verification protocol* consists of a nonempty finite common board alphabet $C$, and for each holder a deterministic decoder $D_v:T_v\times C\to X_v$ and a deterministic check $V_v:T_v\times C\to\{0,1\}$. Every holder sees only its own report, the common board $c$ and the public input. For a target $\Phi$ on a set of profiles:
--
--   - *Completeness*: $\forall P\ \exists c\in C\ \forall v:\ V_v(P_v,c)=1$ and $D_v(P_v,c)=\Phi_v(P)$ (one common board for everybody).
--   - *Soundness*: $\forall P\ \forall c:\ (\forall v\ V_v(P_v,c)=1)\Rightarrow(\forall v\ D_v(P_v,c)=\Phi_v(P))$.
--
--   The board cost is $\ell(C)=\lceil\log_2|C|\rceil$, and $\mathrm{JVC}^b_\xi(\Phi)$ is the minimum cost of a complete and sound protocol; $\mathrm{IJVC}=\mathrm{JVC}^I$ (rank outputs) and $\mathrm{EJVC}=\mathrm{JVC}^E$ (exact outputs). The unrestricted domain is $T=\prod_i T_i$ with $T_i$ all weak rows over the $m$ schools; a domain-restricted version uses a product $\prod_i D_i\subseteq T$.
--
--   `JVCge ξ α b Dom K` says $\mathrm{JVC}^b_\xi(\Phi_\alpha)\ge K$ on `Dom` (every complete and sound protocol costs at least $K$); `JVCle ξ α b Dom K` says $\mathrm{JVC}^b_\xi(\Phi_\alpha)\le K$ (some protocol costs at most $K$). Together they express the minimum without an infimum over a possibly empty set.
--
--   **Formalization Note.** The generic `VerifProtocol R X C` has decoders and checks typed `R v → C → X v` and `R v → C → Bool`, so a holder cannot see another holder's report. In the public-priority instance the report type is `Fin m → ℕ` (all rows, the domain being a `Set` of profiles), the output type is `Out m b`, and the board alphabet is `Fin c` with cost `Nat.clog 2 c`; every finite nonempty alphabet is in bijection with some `Fin c`, and `Fin 0` cannot satisfy completeness on a nonempty domain.
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 5 (public input, cost at fixed ξ, sup over Ξ_{n,m}); p. 6 (Joint-verification complexity)

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model

namespace MatchIndiff.PublicSM

/-- A board verification protocol (p. 6) for report holders `v : V` with report types `R v` and
local output alphabets `X v`, over a common board alphabet `C`: each holder has a deterministic
decoder `D_v : R_v × C → X_v` and a deterministic check `V_v : R_v × C → {0, 1}`; both see only
the holder's own report and the common board (the public input is fixed and implicit). -/
structure VerifProtocol {V : Type*} (R : V → Type*) (X : V → Type*) (C : Type*) where
  /-- local decoders -/
  dec : (v : V) → R v → C → X v
  /-- local checks -/
  chk : (v : V) → R v → C → Bool

/-- Completeness on a set `Dom` of profiles: for every profile one common board makes all checks
accept and all decoders correct. -/
def VerifProtocol.Complete {V : Type*} {R X : V → Type*} {C : Type*}
    (p : VerifProtocol R X C) (Dom : Set ((v : V) → R v)) (Φ : ((v : V) → R v) → (v : V) → X v) :
    Prop :=
  ∀ P ∈ Dom, ∃ c : C, ∀ v, p.chk v (P v) c = true ∧ p.dec v (P v) c = Φ P v

/-- Soundness on `Dom`: for every profile and every board, if all checks accept then all decoders
are correct. -/
def VerifProtocol.Sound {V : Type*} {R X : V → Type*} {C : Type*}
    (p : VerifProtocol R X C) (Dom : Set ((v : V) → R v)) (Φ : ((v : V) → R v) → (v : V) → X v) :
    Prop :=
  ∀ P ∈ Dom, ∀ c : C, (∀ v, p.chk v (P v) c = true) → ∀ v, p.dec v (P v) c = Φ P v

/-- A joint verification protocol for the target `Φ` on `Dom`: complete and sound. -/
def VerifProtocol.IsJV {V : Type*} {R X : V → Type*} {C : Type*}
    (p : VerifProtocol R X C) (Dom : Set ((v : V) → R v)) (Φ : ((v : V) → R v) → (v : V) → X v) :
    Prop :=
  p.Complete Dom Φ ∧ p.Sound Dom Φ

/-- The unrestricted student report domain `T = ∏_i T_i`: every student reports a weak row
over the `m` schools. -/
def fullDomain (n m : ℕ) : Set (Fin n → Fin m → ℕ) :=
  {P | ∀ i, IsRow (P i)}

/-- A public-priority joint verification protocol at public input `ξ` for the selector `Φ_α`
with output type `b`, on the profile set `Dom`, with board alphabet `Fin c` (cost
`⌈log₂ c⌉ = Nat.clog 2 c`). Only students hold reports and check (`V = N`). -/
def IsPublicJV {n m c : ℕ} (ξ : PublicInput n m) (α : StabKind) (b : OutKind)
    (Dom : Set (Fin n → Fin m → ℕ))
    (p : VerifProtocol (fun _ : Fin n => Fin m → ℕ) (fun _ : Fin n => Out m b) (Fin c)) : Prop :=
  p.IsJV Dom (fun P i => phiOut α ξ b P i)

/-- `JVC^b_ξ(Φ_α) ≥ K` on `Dom`: every joint verification protocol has board cost at least `K`. -/
def JVCge {n m : ℕ} (ξ : PublicInput n m) (α : StabKind) (b : OutKind)
    (Dom : Set (Fin n → Fin m → ℕ)) (K : ℕ) : Prop :=
  ∀ (c : ℕ) (p : VerifProtocol (fun _ : Fin n => Fin m → ℕ) (fun _ : Fin n => Out m b) (Fin c)),
    IsPublicJV ξ α b Dom p → K ≤ Nat.clog 2 c

/-- `JVC^b_ξ(Φ_α) ≤ K` on `Dom`: some joint verification protocol has board cost at most `K`. -/
def JVCle {n m : ℕ} (ξ : PublicInput n m) (α : StabKind) (b : OutKind)
    (Dom : Set (Fin n → Fin m → ℕ)) (K : ℕ) : Prop :=
  ∃ (c : ℕ) (p : VerifProtocol (fun _ : Fin n => Fin m → ℕ) (fun _ : Fin n => Out m b) (Fin c)),
    IsPublicJV ξ α b Dom p ∧ Nat.clog 2 c ≤ K

end MatchIndiff.PublicSM


