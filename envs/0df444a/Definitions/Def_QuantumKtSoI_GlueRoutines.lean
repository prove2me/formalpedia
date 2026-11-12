-- Prove2me | Definitions.Def_QuantumKtSoI_GlueRoutines
-- name    : QuantumKtSoI_GlueRoutines
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:34:37.815051+00:00
-- url     : https://prove2.me/theorems/acf7d6c8-056b-4dba-af3b-44bd099dae33
-- title:
--   Admissible glue routines for the constructor $\mathrm{SEQ}_g$
-- statement:
--   The three **glue modes** $g\in\{\mathrm{feed},\mathrm{cat},\mathrm{pair}\}$ are the pairs of maps
--   $$\alpha_{\mathrm{feed}}(x,u)=\langle x,u\rangle,\ \beta_{\mathrm{feed}}(x,u,v)=v;\qquad \alpha_{\mathrm{cat}}(x,u)=xu,\ \beta_{\mathrm{cat}}(x,u,v)=uv;\qquad \alpha_{\mathrm{pair}}(x,u)=u,\ \beta_{\mathrm{pair}}(x,u,v)=\langle u,v\rangle .$$
--   A **routine** is a deterministic classical finite control over its own tapes: source tapes, one target tape and work tapes. A set $G$ of **glue routines** gives, for every mode $g$, a routine writing $\alpha_g(x,u)$ (sources: the input tape holding $x$ and the output tape of the first component holding $u$; target: the input tape of the second component) and a routine writing $\beta_g(x,u,v)$ (sources $x,u,v$; target: the composite's output tape), together with a constant $c_0$.
--
--   $G$ is **admissible** (p.24) when $c_0\ge1$ and every routine
--   1. obeys the local rules of Definition 3.1 on its tapes (it writes $\vdash$ exactly where it scans $\vdash$, writes back the input symbol, writes only alphabet symbols, and moves a head left only on an active tape not scanning $\vdash$);
--   2. whenever the heads of the source tapes start within distance $\ell$ of cell $0$ (sources of the stated shape, target and work tapes blank), exits within $c_0(|x|+|u|+|v|+\ell+1)$ steps, leaving the glue value followed only by blanks on the target, all its heads on cell $0$, and the sources unchanged.
--
--   When the composite machine runs a routine, every qubit head whose companion is a routine tape receives the same move (p.24).
--
--   **Formalization Note** The paper fixes its glue routines "once and for all" but describes them only by these properties; every statement of the mission quantifies over all admissible sets, and the goal asserts that one exists.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), §3.2, p.24

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_Machine

open Classical

noncomputable section

namespace QuantumKtSoI

/-- The three glue modes `feed`, `cat`, `pair` (p.24). -/
inductive Glue
  | feed
  | cat
  | pair
  deriving DecidableEq

/-- `α_g(x, u)`, the input of the second component (p.24):
`α_feed(x,u) = ⟨x,u⟩`, `α_cat(x,u) = xu`, `α_pair(x,u) = u`. -/
def Glue.alpha : Glue → List Bool → List Bool → List Bool
  | .feed, x, u => QuantumKtSoI.pair x u
  | .cat, x, u => x ++ u
  | .pair, _, u => u

/-- `β_g(x, u, v)`, the output of the composite (p.24):
`β_feed(x,u,v) = v`, `β_cat(x,u,v) = uv`, `β_pair(x,u,v) = ⟨u,v⟩`. -/
def Glue.beta : Glue → List Bool → List Bool → List Bool → List Bool
  | .feed, _, _, v => v
  | .cat, _, u, v => u ++ v
  | .pair, _, u, v => QuantumKtSoI.pair u v

/-- The tapes of a glue routine with `n` source tapes and `w` work tapes: the sources, the one
target tape, and the work tapes. -/
inductive RTape (n w : ℕ)
  | src (i : Fin n)
  | tgt
  | wk (i : Fin w)
  deriving DecidableEq, Fintype

/-- A **routine** (p.20, p.24): a deterministic classical finite control over its own tapes
(`n` source tapes, one target tape, `nWork` work tapes with alphabets `walph`), with an entry
state `start`. A transition reads the scanned symbols of the active tapes `act r` (inactive
coordinates masked to `#`) and gives the next state (`none` = exit), the symbols written on the
active tapes, and a move of every routine head. -/
structure Routine (n : ℕ) where
  R : Type
  [instF : Fintype R]
  [instD : DecidableEq R]
  nWork : ℕ
  walph : Fin nWork → Finset Sym
  start : R
  act : R → Finset (RTape n nWork)
  δ : R → (RTape n nWork → Sym) → Option R × (RTape n nWork → Sym) × (RTape n nWork → Move)

attribute [instance] Routine.instF Routine.instD

/-- The alphabet `{⊢, 0, 1, #}` of input, output and output-copy tapes. -/
def ioAlph : Finset Sym := {Sym.mark, Sym.b0, Sym.b1, Sym.blank}

/-- A tape holding `⊢ w` followed by blanks, every negative cell blank. -/
def stringTape (w : List Bool) : ℤ → Sym := fun i =>
  if i = 0 then Sym.mark
  else if 1 ≤ i ∧ i ≤ w.length then Sym.ofBit (w.getD (i - 1).toNat false)
  else Sym.blank

/-- The contents of a classical output tape whose output is `u`: `⊢` at cell `0`, `u` on cells
`1, …, |u|`, `#` on cell `|u| + 1`, arbitrary symbols of `{0, 1, #}` beyond, and blanks at negative
cells. -/
def OutputShaped (u : List Bool) (c : ℤ → Sym) : Prop :=
  c 0 = Sym.mark ∧ (∀ i : ℕ, i < u.length → c ((i : ℤ) + 1) = Sym.ofBit (u.getD i false)) ∧
    c ((u.length : ℤ) + 1) = Sym.blank ∧
    (∀ j : ℤ, (u.length : ℤ) + 1 < j → c j = Sym.b0 ∨ c j = Sym.b1 ∨ c j = Sym.blank) ∧
    ∀ j : ℤ, j < 0 → c j = Sym.blank

namespace Routine

variable {n : ℕ} (ρ : Routine n)

/-- The alphabet of a routine tape. -/
def alphOf : RTape n ρ.nWork → Finset Sym
  | .src _ => ioAlph
  | .tgt => ioAlph
  | .wk i => ρ.walph i

/-- Masking of inactive coordinates. -/
def mask (r : ρ.R) (σ : RTape n ρ.nWork → Sym) : RTape n ρ.nWork → Sym :=
  fun t => if t ∈ ρ.act r then σ t else Sym.blank

/-- A routine configuration: the current state (`none` once exited), contents and heads. -/
abbrev Conf := Option ρ.R × (RTape n ρ.nWork → ℤ → Sym) × (RTape n ρ.nWork → ℤ)

/-- One step of the routine; an exited configuration stays unchanged. -/
def rstep : ρ.Conf → ρ.Conf
  | (none, c, h) => (none, c, h)
  | (some r, c, h) =>
      let out := ρ.δ r (ρ.mask r fun t => c t (h t))
      (out.1, fun t => if t ∈ ρ.act r then Function.update (c t) (h t) (out.2.1 t) else c t,
        fun t => h t + (out.2.2 t).toInt)

/-- The local rules of Definition 3.1(ii),(iv) on the routine's tapes: work alphabets contain `⊢`
and `#`; on every transition row with legal scanned symbols, written symbols lie in the alphabet,
`⊢` is written exactly where it is scanned, the symbol scanned on the input tape (source `0`) is
written back, and a head moves left only if its tape is active and does not scan `⊢`. -/
def LocalRules {n : ℕ} (ρ : Routine (n + 1)) : Prop :=
  (∀ i, Sym.mark ∈ ρ.walph i ∧ Sym.blank ∈ ρ.walph i) ∧
    ∀ r σ, (∀ t ∈ ρ.act r, σ t ∈ ρ.alphOf t) →
      let out := ρ.δ r (ρ.mask r σ)
      (∀ t ∈ ρ.act r, out.2.1 t ∈ ρ.alphOf t) ∧
        (∀ t ∈ ρ.act r, (out.2.1 t = Sym.mark ↔ σ t = Sym.mark)) ∧
        (RTape.src 0 ∈ ρ.act r → out.2.1 (RTape.src 0) = σ (RTape.src 0)) ∧
        ∀ t, out.2.2 t = Move.L → t ∈ ρ.act r ∧ σ t ≠ Sym.mark

/-- The routine **correctly writes `out` from the sources `srcs` within the constant `c0`** (p.24):
for every `ℓ`, every source contents of the right shape (source `0` the input tape `⊢ x # # ⋯`,
the other sources output tapes holding `srcs i`), and all source heads in `[0, ℓ]`, with the
target and work tapes blank and their heads at `0`, the run from `start` exits within
`c0 · (Σᵢ |srcs i| + ℓ + 1)` steps, leaving `⊢ out` followed only by blanks on the target, every
routine head on cell `0`, and the source contents unchanged. -/
def Correct (c0 : ℕ) (srcs : Fin (n + 1) → List Bool) (out : List Bool) (ρ : Routine (n + 1)) :
    Prop :=
  ∀ ℓ : ℕ, ∀ cs : Fin (n + 1) → ℤ → Sym, cs 0 = stringTape (srcs 0) →
    (∀ i, i ≠ 0 → OutputShaped (srcs i) (cs i)) →
    ∀ h : Fin (n + 1) → ℤ, (∀ i, 0 ≤ h i ∧ h i ≤ ℓ) →
      let c₀ : RTape (n + 1) ρ.nWork → ℤ → Sym := fun t =>
        match t with
        | .src i => cs i
        | _ => fun j => if j = 0 then Sym.mark else Sym.blank
      let h₀ : RTape (n + 1) ρ.nWork → ℤ := fun t =>
        match t with
        | .src i => h i
        | _ => 0
      let fin := ρ.rstep^[c0 * ((∑ i, (srcs i).length) + ℓ + 1)] (some ρ.start, c₀, h₀)
      fin.1 = none ∧ fin.2.1 RTape.tgt = stringTape out ∧ (∀ t, fin.2.2 t = 0) ∧
        ∀ i, fin.2.1 (RTape.src i) = cs i

end Routine

/-- A set of **glue routines** (p.24): for each glue mode `g` a routine `α g` writing `α_g(x,u)`
from the sources `x` (the input tape) and `u` (the first component's output tape) onto the target
(the second component's input tape), a routine `β g` writing `β_g(x,u,v)` from the sources `x`,
`u`, `v` onto the target (the composite's output tape), and the constant `c0`. -/
structure GlueRoutines where
  α : Glue → Routine 2
  β : Glue → Routine 3
  c0 : ℕ

/-- **Admissible glue routines** (p.24): `c0 ≥ 1`, and for each mode `g` the routines obey the
local rules of Definition 3.1 and, whenever the heads of the tapes holding `x`, `u` and `v` start
within distance `ℓ` of cell `0`, write `α_g(x,u)` (resp. `β_g(x,u,v)`) in at most
`c0(|x|+|u|+|v|+ℓ+1)` steps, ending with all their heads on cell `0`.

**Formalization Note** The paper fixes its routines "once and for all" only by these properties;
every statement of the mission quantifies over all admissible routine sets. -/
def GlueRoutines.Admissible (G : GlueRoutines) : Prop :=
  1 ≤ G.c0 ∧ ∀ g : Glue,
    (G.α g).LocalRules ∧ (G.β g).LocalRules ∧
      (∀ x u, (G.α g).Correct G.c0 ![x, u] (g.alpha x u)) ∧
      ∀ x u v, (G.β g).Correct G.c0 ![x, u, v] (g.beta x u v)

end QuantumKtSoI


