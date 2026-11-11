-- Prove2me | Definitions.Def_PermDiameter_Binary_WreathConstruction
-- name    : PermDiameter_Binary_WreathConstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:11:31.936861+00:00
-- url     : https://prove2.me/theorems/81a238fb-9ee6-4d89-9548-330974deab2e
-- title:
--   Step 2 of the reduction: $G_2=G_1\wr C_r$, local generators, transversals, fillers, bridges, entries, exits and word shapes
-- statement:
--   On top of Step 1, Step 2 chooses (`WreathData`): $r\le10d_1^3$ with $r\ge1$; a **stabilizer position** $s(\omega)\in C_r$ for every point $\omega\in\Omega_1$; a point $\omega_i$ moved by $g_1$ and $\omega_j=\omega_i g_1$; the position $x_*=s(\omega_i)^{-1}s(\omega_j)$ and the special positions $S=\{1\}\cup S'\cup\{x_*\}$, $S'=\{s(\omega):\omega\in\Omega_1\}$, satisfying (i), (ii) of Lemma 3.4. With $I_t=S\cap St^{-1}=\{x\in S:xt\in S\}$:
--
--   1. **Local generators** $\Lambda_x\subseteq G_1$ and $H_x=\langle\Lambda_x\rangle$: $\Lambda_1=\{1\}$; $\Lambda_{x_*}=\Sigma_1$; $\Lambda_{s(\omega)}$ generates $\mathrm{Stab}_{G_1}(\omega)$ with $\operatorname{diam}\le d_1$; at every generic position $x\notin S$ the same set $\Lambda_{\mathrm{gen}}$, generating $G_1$ with $\operatorname{diam}(G_1,\Lambda_{\mathrm{gen}})\le d_1$.
--   2. **Transversals**: $LT_1=RT_1=\varnothing$; for $x\in S\setminus\{1\}$, $LT_x$ and $RT_x$ are a left and a right transversal of $H_x$ in $G_1$, both containing $1$. For $x,y\in S$ distinct, $T_{x,y}=RT_x\cup LT_y$.
--   3. $G_2=G_1\wr C_r$ (all $(f,t)$ with values in $G_1$). **Fillers** $\Gamma=\bigcup_x\{(\delta^x_a,1):a\in\Lambda_x\}$, where $\delta^x_a$ has value $a$ at $x$ and $1$ elsewhere. **Bridges** $\Gamma_\diamond$: all $(h,t)$ with $t\ne1$, $h(x)\in T_{x,xt}$ for $x\in I_t$ and $h(x)=1$ for $x\notin I_t$. $\Sigma_2=\Gamma\cup\Gamma_\diamond$.
--   4. **Entries** $\Gamma_\triangleright$: bridges $(h,y)$ with $y\in S\setminus\{1\}$ and, if $y\in S'$, $h(1)\notin g_1H_y$. **Exits** $\Gamma_\triangleleft=\{(1,y^{-1}):y\in S\setminus\{1\}\}$.
--   5. **Word shapes**: $\Gamma^*\Gamma_\diamond\Gamma^*$ (fillers, one bridge, fillers) and $\Gamma^*\Gamma_\triangleright\Gamma^*\Gamma_\triangleleft\Gamma^*$ (fillers, one entry, fillers, one exit, fillers), with their values (products in order), lengths, and the number of fillers at a position.
--
--   Every choice with these properties is admissible; the paper's (Lemma 2.3's generating sets and transversals, Lemma 3.4's positions after an enumeration of $\Omega_1$) is one of them.
--
--   **Formalization Note.** $C_r$ is `Multiplicative (ZMod r)`; positions are indexed by the points of $\Omega_1$ directly (the paper's $s_k$ is $s(\omega_k)$ for an enumeration $\omega_1,\dots,\omega_{d_1}$). $G_2$ is a subset of the wreath product `Wreath (Perm Ω₁) (C_r)`. A filler letter is recorded as a pair (position $x$, generator $a\in\Lambda_x$) standing for $(\delta^x_a,1)$, so "fillers at the position $x$" counts letters tagged $x$; `BridgeWord` and `EntryExitWord` record the shape explicitly.
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), pp. 15–16 (§3.2.1–3.2.2: special positions, G2, fillers, transversals, bridges), p. 18 (§3.2.3: entries and exits), p. 17 (word classes Γ*Γ⋄Γ*)

import Mathlib
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_Wreath
import Definitions.Def_PermDiameter_Binary_Parameters
import Definitions.Def_PermDiameter_Binary_LengthGap

namespace PermDiameter.Binary

/-!
# Step 2 of the reduction: the wreath product `G₂ = G₁ ≀ C_r` (Lohrey–Thumm, §3.2, pp. 14–18)

On top of the Step 1 data `D`, Step 2 chooses: positions `s : Ω₁ → C_r` from Lemma 3.4 (the
paper enumerates `Ω₁ = {ω₁, …, ω_{d₁}}` and writes `s_k` for the position of `ω_k`; here the
positions are indexed by the points themselves), a point `ω_i` moved by `g₁` with
`ω_j = ω_i g₁`, local generating sets `Λ_x`, and transversals `LT_x`, `RT_x`. The structure
`WreathData D` bundles **every admissible choice**, with exactly the properties §3.2 states.
-/

open Equiv

/-- A word in `Γ* Γ⋄ Γ*`: fillers `u`, one bridge `b`, fillers `v`. A filler letter is recorded as
the pair (position `x`, local generator `a`), standing for the filler `(δ^x_a, 1)`. -/
structure BridgeWord (A P : Type) where
  /-- the fillers before the bridge -/
  u : List (P × A)
  /-- the bridge -/
  b : Wreath A P
  /-- the fillers after the bridge -/
  v : List (P × A)

/-- A word in `Γ* Γ▷ Γ* Γ◁ Γ*`: fillers `u`, one entry `e`, fillers `v`, one exit `x`,
fillers `w`. Filler letters are (position, local generator) pairs as in `BridgeWord`. -/
structure EntryExitWord (A P : Type) where
  /-- the fillers before the entry -/
  u : List (P × A)
  /-- the entry -/
  e : Wreath A P
  /-- the fillers between the entry and the exit -/
  v : List (P × A)
  /-- the exit -/
  x : Wreath A P
  /-- the fillers after the exit -/
  w : List (P × A)

variable {d0 : ℕ} {Sig0 : Finset (Perm (Fin d0))} {g0 : Perm (Fin d0)} {k0 : ℕ}

/-- An admissible choice of the Step 2 data over the Step 1 data `D` (§3.2.1–3.2.2):
* `r ≤ 10 d₁³` and positions `s : Ω₁ → C_r` with properties (i), (ii) of Lemma 3.4 for the pair
  `(ω_i, ω_j)`, where `ω_i` is a point moved by `g₁` and `ω_j = ω_i g₁`;
* local generators: `Λ_1 = {1}`; `Λ_{x∗} = Σ₁`; for every point `ω`, `Λ_{s(ω)}` generates
  `Stab_{G₁}(ω)` with `diam ≤ d₁`; one set `Λ_gen` generating `G₁` with `diam(G₁, Λ_gen) ≤ d₁`
  is used at every generic position `x ∉ S`;
* transversals: `LT_1 = RT_1 = ∅`; for `x ∈ S ∖ {1}`, `LT_x` (resp. `RT_x`) is a left (resp.
  right) transversal of `H_x = ⟨Λ_x⟩` in `G₁` containing `1`. -/
structure WreathData (D : LengthGapData Sig0 g0 k0) where
  /-- the order `r` of the cyclic group `C_r` of positions -/
  r : ℕ
  /-- `C_r` is a group of order `r ≥ 1` -/
  hr0 : 0 < r
  /-- `r ≤ 10 d₁³` (Lemma 3.4) -/
  hr : r ≤ 10 * D.d1 ^ 3
  /-- the stabilizer position `s(ω)` of each point `ω ∈ Ω₁` -/
  s : Omega1 d0 D.dc → Pos r
  /-- the point `ω_i`, moved by `g₁` -/
  ωi : Omega1 d0 D.dc
  /-- `ω_i g₁ ≠ ω_i` -/
  hωi : D.g1 ωi ≠ ωi
  /-- Lemma 3.4 (i), (ii) for `x∗ = s(ω_i)⁻¹ s(ω_j)`, `ω_j = ω_i g₁` -/
  hS : SpecialPositionsProp s ωi (D.g1 ωi)
  /-- the local generators `Λ_x ⊆ G₁` at every position -/
  Lam : Pos r → Finset (Perm (Omega1 d0 D.dc))
  /-- `Λ_1 = {1}` -/
  hLam1 : Lam 1 = {1}
  /-- `Λ_{x∗} = Σ₁` -/
  hLamStar : Lam ((s ωi)⁻¹ * s (D.g1 ωi)) = D.Sig1
  /-- `Λ_{s(ω)}` generates `Stab_{G₁}(ω)` with diameter at most `d₁` -/
  hLamStab : ∀ ω, Subgroup.closure (Lam (s ω) : Set (Perm (Omega1 d0 D.dc))) = D.Stab ω ∧
    diamOn (D.Stab ω : Set (Perm (Omega1 d0 D.dc))) (Lam (s ω) : Set (Perm (Omega1 d0 D.dc)))
      ≤ (D.d1 : ℕ∞)
  /-- the generating set of `G₁` used at all generic positions -/
  LamGen : Finset (Perm (Omega1 d0 D.dc))
  /-- `Λ_gen` generates `G₁` with diameter at most `d₁` -/
  hLamGen : Subgroup.closure (LamGen : Set (Perm (Omega1 d0 D.dc))) = D.G1 ∧
    diamOn (D.G1 : Set (Perm (Omega1 d0 D.dc))) (LamGen : Set (Perm (Omega1 d0 D.dc)))
      ≤ (D.d1 : ℕ∞)
  /-- `Λ_x = Λ_gen` at every generic position `x ∉ S` -/
  hLamGeneric : ∀ x, x ∉ specialSet s ωi (D.g1 ωi) → Lam x = LamGen
  /-- the left transversals `LT_x` -/
  LT : Pos r → Set (Perm (Omega1 d0 D.dc))
  /-- the right transversals `RT_x` -/
  RT : Pos r → Set (Perm (Omega1 d0 D.dc))
  /-- `LT_1 = ∅` -/
  hLT1 : LT 1 = ∅
  /-- `RT_1 = ∅` -/
  hRT1 : RT 1 = ∅
  /-- for `x ∈ S ∖ {1}`, `LT_x` is a left transversal of `H_x` in `G₁` containing `1` -/
  hLT : ∀ x ∈ specialSet s ωi (D.g1 ωi), x ≠ 1 →
    IsLeftTransversal (LT x) (Subgroup.closure (Lam x : Set (Perm (Omega1 d0 D.dc)))) D.G1 ∧
      (1 : Perm (Omega1 d0 D.dc)) ∈ LT x
  /-- for `x ∈ S ∖ {1}`, `RT_x` is a right transversal of `H_x` in `G₁` containing `1` -/
  hRT : ∀ x ∈ specialSet s ωi (D.g1 ωi), x ≠ 1 →
    IsRightTransversal (RT x) (Subgroup.closure (Lam x : Set (Perm (Omega1 d0 D.dc)))) D.G1 ∧
      (1 : Perm (Omega1 d0 D.dc)) ∈ RT x

namespace WreathData

variable {D : LengthGapData Sig0 g0 k0} (W : WreathData D)

/-- The point `ω_j = ω_i g₁`. -/
def ωj : Omega1 d0 D.dc := D.g1 W.ωi

/-- The position `x∗ = s_i⁻¹ s_j`. -/
def xstar : Pos W.r := (W.s W.ωi)⁻¹ * W.s W.ωj

/-- The special positions `S = {1, s_1, …, s_{d₁}, x∗}`. -/
def S : Finset (Pos W.r) := specialSet W.s W.ωi W.ωj

/-- The stabilizer positions `S' = {s_1, …, s_{d₁}}`. -/
def S' : Finset (Pos W.r) := Finset.univ.image W.s

/-- `I_t = S ∩ S t⁻¹ = {x ∈ S : x t ∈ S}`. -/
def I (t : Pos W.r) : Finset (Pos W.r) := W.S.filter (fun x => x * t ∈ W.S)

/-- `H_x = ⟨Λ_x⟩ ≤ G₁`. -/
def H (x : Pos W.r) : Subgroup (Perm (Omega1 d0 D.dc)) :=
  Subgroup.closure (W.Lam x : Set (Perm (Omega1 d0 D.dc)))

/-- `T_{x,y} = RT_x ∪ LT_y` (used for distinct `x, y ∈ S`). -/
def T (x y : Pos W.r) : Set (Perm (Omega1 d0 D.dc)) := W.RT x ∪ W.LT y

/-- `G₂ = G₁ ≀ C_r`, inside the wreath product `Sym(Ω₁) ≀ C_r`: all `(f, t)` with every value
`f(x) ∈ G₁`. -/
def G2 : Set (Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r)) := {p | ∀ x, p.f x ∈ D.G1}

/-- The element `(δ^x_a, 1)` of the coordinate subgroup at `x`. -/
def filler (x : Pos W.r) (a : Perm (Omega1 d0 D.dc)) : Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r) :=
  ⟨Pi.mulSingle x a, 1⟩

/-- The fillers `Γ = ⋃_x {(δ^x_a, 1) : a ∈ Λ_x}`. -/
def Gamma : Set (Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r)) :=
  {p | ∃ x, ∃ a ∈ W.Lam x, p = W.filler x a}

/-- `(h, t)` is a **bridge** (`∈ Γ⋄,t`): `t ≠ 1`, `h(x) ∈ T_{x, x t}` for `x ∈ I_t`, and
`h(x) = 1` for `x ∉ I_t`. -/
def IsBridge (p : Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r)) : Prop :=
  p.t ≠ 1 ∧ (∀ x ∈ W.I p.t, p.f x ∈ W.T x (x * p.t)) ∧ ∀ x, x ∉ W.I p.t → p.f x = 1

/-- The generating set `Σ₂ = Γ ∪ Γ⋄` of `G₂`. -/
def Sig2 : Set (Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r)) := W.Gamma ∪ {p | W.IsBridge p}

/-- `(h, y)` is an **entry** (`∈ Γ▷`, §3.2.3): a bridge with shift `y ∈ S ∖ {1}` and, if
`y ∈ S'`, `h(1) ∉ g₁ H_y`. -/
def IsEntry (p : Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r)) : Prop :=
  W.IsBridge p ∧ p.t ∈ W.S ∧ p.t ≠ 1 ∧ (p.t ∈ W.S' → ∀ h ∈ W.H p.t, p.f 1 ≠ D.g1 * h)

/-- `p` is an **exit** (`∈ Γ◁`): `p = (1, y⁻¹)` for some `y ∈ S ∖ {1}`. -/
def IsExit (p : Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r)) : Prop :=
  ∃ y ∈ W.S, y ≠ 1 ∧ p = ⟨fun _ => 1, y⁻¹⟩

/-- Every letter `(x, a)` of a filler word is a filler: `a ∈ Λ_x`. -/
def FillerWord (u : List (Pos W.r × Perm (Omega1 d0 D.dc))) : Prop :=
  ∀ xa ∈ u, xa.2 ∈ W.Lam xa.1

/-- The value of a filler word: the product of its fillers `(δ^x_a, 1)` in order. -/
def fillerValue (u : List (Pos W.r × Perm (Omega1 d0 D.dc))) :
    Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r) :=
  (u.map fun xa => W.filler xa.1 xa.2).prod

/-- A word of `Γ* Γ⋄ Γ*`: fillers, a bridge, fillers. -/
def BridgeWordValid (w : BridgeWord (Perm (Omega1 d0 D.dc)) (Pos W.r)) : Prop :=
  W.FillerWord w.u ∧ W.IsBridge w.b ∧ W.FillerWord w.v

/-- The element represented by a word of `Γ* Γ⋄ Γ*`. -/
def bridgeWordValue (w : BridgeWord (Perm (Omega1 d0 D.dc)) (Pos W.r)) :
    Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r) :=
  W.fillerValue w.u * w.b * W.fillerValue w.v

/-- The length `|w|` of a word of `Γ* Γ⋄ Γ*`. -/
def bridgeWordLength (w : BridgeWord (Perm (Omega1 d0 D.dc)) (Pos W.r)) : ℕ :=
  w.u.length + 1 + w.v.length

/-- A word of `Γ* Γ▷ Γ* Γ◁ Γ*`: fillers, an entry, fillers, an exit, fillers. -/
def EntryExitWordValid (w : EntryExitWord (Perm (Omega1 d0 D.dc)) (Pos W.r)) : Prop :=
  W.FillerWord w.u ∧ W.IsEntry w.e ∧ W.FillerWord w.v ∧ W.IsExit w.x ∧ W.FillerWord w.w

/-- The element represented by a word of `Γ* Γ▷ Γ* Γ◁ Γ*`. -/
def entryExitWordValue (w : EntryExitWord (Perm (Omega1 d0 D.dc)) (Pos W.r)) :
    Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r) :=
  W.fillerValue w.u * w.e * W.fillerValue w.v * w.x * W.fillerValue w.w

/-- The length `|w|` of a word of `Γ* Γ▷ Γ* Γ◁ Γ*`. -/
def entryExitWordLength (w : EntryExitWord (Perm (Omega1 d0 D.dc)) (Pos W.r)) : ℕ :=
  w.u.length + 1 + w.v.length + 1 + w.w.length

/-- The number of fillers of `w` at the position `x` (letters `(x, a)` among `u`, `v`, `w`). -/
def fillersAt (w : EntryExitWord (Perm (Omega1 d0 D.dc)) (Pos W.r)) (x : Pos W.r) : ℕ :=
  (w.u ++ w.v ++ w.w).countP (fun xa => decide (xa.1 = x))

end WreathData

end PermDiameter.Binary


