-- Prove2me | Definitions.Def_ImplicitParityWL_Supplement_RegisterProgram
-- name    : ImplicitParityWL_Supplement_RegisterProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:27:06.578842+00:00
-- url     : https://prove2.me/theorems/06712005-e434-4202-ab79-1e8401f0acf5
-- title:
--   Register programs, acceptance and their encoding
-- statement:
--   Let $s\ge2$, $\ell\ge1$ and $A=\mathbb F_2^\ell$. A **register program** $R=(P,s)$ has a finite set $P$ of control locations containing two distinct locations $\mathrm{accept}$ and $\mathrm{reject}$, $s$ registers over $A$, and finitely many guarded commands, each assigned to a location $p$. A guard is $\varphi=\bigwedge_{i\in[s]}a_i\in D_i$ with $D_i\subseteq A$, and a command is
--
--   1. "when at $p$ and $\varphi$ holds: $a\leftarrow T(a)$; goto $q$", with $T(a)_i=a_{\sigma(i)}+\delta_i$ for a permutation $\sigma$ of $[s]$ and $\delta\in A^s$; or
--   2. "when at $p$ and $\varphi$ holds: fork $q$ and $r$".
--
--   A configuration $(p,a)\in P\times A^s$ **accepts** if $p=\mathrm{accept}$; or $p\notin\{\mathrm{accept},\mathrm{reject}\}$ and some assign command at $p$ whose guard holds for $a$ leads to an accepting $(q,T(a))$; or some fork command at $p$ whose guard holds has both $(q,a)$ and $(r,a)$ accepting. Acceptance is the least such notion: it is witnessed by a finite derivation tree. A query $(p^*,a^*)$ accepts iff $(p^*,a^*)$ does.
--
--   **Encoding** (§8.4). An encoding of $R$ and a query lists $s$, $\ell$, the number $w$ of locations (indexed by numbers), $\mathrm{accept}$, $\mathrm{reject}$, the number $r$ of commands and the commands, each with its location, its $s$ guard sets, and, for an assign command, $\sigma$, $\delta$ and the target, for a fork the two targets; then the query. Each guard set $D_i$ is given either by listing its elements or by its membership string of length $2^\ell$, and the choice is free for each set separately. Its bit length is $L$.
--
--   Register programs are the intermediate language between Turing machines and implicit parity systems (Theorem 8.6).
--
--   **Formalization Note** Registers are indexed by $\mathrm{Fin}\,s$ and locations by $\mathrm{Fin}\,w$. The commands of all locations form one list, each command carrying its location; $r$ is the length of the list. Numbers are written in the self-delimiting code of the published `VariableWL` definition, and register values as their $\ell$ bits.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Definition 8.1, pp.42–43; §8.4, p.47

import Mathlib
import Definitions.Def_VariableWL

namespace ImplicitParityWL

namespace Supplement

open OAI.VariableWL

/-- The register alphabet `A = 𝔽₂^ℓ` (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the
Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026,
Definition 8.1, p.42). -/
abbrev RegVal (ℓ : ℕ) := Fin ℓ → ZMod 2

/-- A **guarded command** of a register program with `s` registers over `A = 𝔽₂^ℓ` and control
locations `Fin w` (Definition 8.1, pp.42–43), together with the location `p` it is assigned to.
Both forms carry a guard `φ = ⋀_{i ∈ [s]} a_i ∈ D_i` with `D_i ⊆ A`.

* `assign p D σ δ q`: "when at location `p` and `φ` holds: `a ← T(a)`; goto `q`", with
  `T(a)_i = a_{σ(i)} + δ_i` for a permutation `σ` of `[s]` and an offset `δ ∈ A^s`.
* `fork p D q r`: "when at location `p` and `φ` holds: fork `q` and `r`".

**Formalization Note** Registers are indexed by `Fin s` (register `i` of the page is `i - 1`). -/
inductive Command (s ℓ w : ℕ) where
  | assign (p : Fin w) (D : Fin s → Finset (RegVal ℓ)) (σ : Equiv.Perm (Fin s)) (δ : Fin s → RegVal ℓ)
      (q : Fin w)
  | fork (p : Fin w) (D : Fin s → Finset (RegVal ℓ)) (q r : Fin w)

/-- A **register program** `R = (P, s)` (Definition 8.1, p.42): `w` control locations `P = Fin w`
containing `accept` and `reject`, `s` registers over `A = 𝔽₂^ℓ`, and a finite list of guarded commands,
each assigned to a location.

**Formalization Note** `accept ≠ reject`: the page halts and accepts at `accept` and halts and rejects
at `reject`, so the two are different locations. `w` is the number of control locations and the length
of `cmds` is the number `r` of guarded commands of Theorem 8.6. -/
structure RegisterProgram (s ℓ : ℕ) where
  /-- The number of control locations. -/
  w : ℕ
  /-- The accepting location. -/
  accept : Fin w
  /-- The rejecting location. -/
  reject : Fin w
  /-- The two halting locations are distinct. -/
  accept_ne_reject : accept ≠ reject
  /-- The guarded commands. -/
  cmds : List (Command s ℓ w)

namespace RegisterProgram

variable {s ℓ : ℕ}

/-- **Acceptance** of a configuration `(p, a)` (Definition 8.1, pp.42–43): `(accept, a)` accepts; at a
location other than `accept` and `reject`, `(p, a)` accepts if some assign command at `p` whose guard
holds leads to an accepting `(q, T(a))`, or some fork command at `p` whose guard holds has both `(q, a)`
and `(r, a)` accepting.

**Formalization Note** This is the least such set (an inductive predicate): acceptance "within
finitely many steps", equivalently a finite derivation tree whose leaves are accepting halts (p.43).
`(reject, a)` never accepts. -/
inductive Accepts (R : RegisterProgram s ℓ) : Fin R.w → (Fin s → RegVal ℓ) → Prop
  | halt (a : Fin s → RegVal ℓ) : Accepts R R.accept a
  | assign {p : Fin R.w} {D : Fin s → Finset (RegVal ℓ)} {σ : Equiv.Perm (Fin s)}
      {δ : Fin s → RegVal ℓ} {q : Fin R.w} {a : Fin s → RegVal ℓ} :
      Command.assign p D σ δ q ∈ R.cmds → p ≠ R.accept → p ≠ R.reject → (∀ i, a i ∈ D i) →
      Accepts R q (fun i => a (σ i) + δ i) → Accepts R p a
  | fork {p : Fin R.w} {D : Fin s → Finset (RegVal ℓ)} {q r : Fin R.w} {a : Fin s → RegVal ℓ} :
      Command.fork p D q r ∈ R.cmds → p ≠ R.accept → p ≠ R.reject → (∀ i, a i ∈ D i) →
      Accepts R q a → Accepts R r a → Accepts R p a

end RegisterProgram

/-- The bits of a register value `x ∈ 𝔽₂^ℓ`, in coordinate order. -/
def regCode {ℓ : ℕ} (x : RegVal ℓ) : Word := List.ofFn fun j => decide (x j = 1)

/-- The index `∑_j x_j 2^j` of a register value, its position in a membership string. -/
def regIndex {ℓ : ℕ} (x : RegVal ℓ) : ℕ := ∑ j : Fin ℓ, (x j).val * 2 ^ j.val

open scoped Classical in
/-- `u` encodes the guard set `D ⊆ A` (§8.4, p.47) in one of the two allowed forms: **listed by
elements** (a tag `0`, the number of elements, then the elements in some order without repetition), or
as a **membership string** of length `2^ℓ` (a tag `1`, then bit `i` saying whether the element of index
`i` lies in `D`). -/
def SetCode {ℓ : ℕ} (D : Finset (RegVal ℓ)) (u : Word) : Prop :=
  (∃ l : List (RegVal ℓ), l.Nodup ∧ l.toFinset = D ∧
      u = false :: (integerCode l.length ++ (l.map regCode).flatten)) ∨
    u = true :: List.ofFn fun i : Fin (2 ^ ℓ) => decide (∃ x ∈ D, regIndex x = i.val)

/-- The explicit listing of a register permutation `σ`: `σ(0), …, σ(s-1)`. -/
def permCode {s : ℕ} (σ : Equiv.Perm (Fin s)) : Word := (List.ofFn fun i => integerCode (σ i).val).flatten

/-- The explicit listing of an offset (or valuation) `δ ∈ A^s`: `δ_0, …, δ_{s-1}`. -/
def valCode {s ℓ : ℕ} (δ : Fin s → RegVal ℓ) : Word := (List.ofFn fun i => regCode (δ i)).flatten

/-- `u` encodes a guarded command (§8.4, p.47): a tag (`0` assign, `1` fork), its location, the `s`
guard sets each in one of the allowed forms, then for an assign command `σ`, `δ` and the target, for a
fork the two targets. -/
def CmdCode {s ℓ w : ℕ} : Command s ℓ w → Word → Prop
  | .assign p D σ δ q, u => ∃ us : Fin s → Word, (∀ i, SetCode (D i) (us i)) ∧
      u = false :: (integerCode p.val ++ (List.ofFn us).flatten ++ permCode σ ++ valCode δ ++
        integerCode q.val)
  | .fork p D q r, u => ∃ us : Fin s → Word, (∀ i, SetCode (D i) (us i)) ∧
      u = true :: (integerCode p.val ++ (List.ofFn us).flatten ++ integerCode q.val ++
        integerCode r.val)

/-- `u` is an **encoding of the register program `R` and the query `(p∗, a∗)`** (§8.4, p.47): `s`, `ℓ`,
the number `w` of locations, `accept`, `reject`, the number `r` of commands, the commands (locations
indexed by numbers, each guard set in either form, `σ` and `δ` listed explicitly), then the query.
Its length is the bit length `L` of Theorem 8.6.

**Formalization Note** The page fixes the content of the encoding, not its bit layout; numbers are the
published self-delimiting `integerCode`. The choice of form is free for every guard set separately. -/
def Encodes {s ℓ : ℕ} (R : RegisterProgram s ℓ) (p : Fin R.w) (a : Fin s → RegVal ℓ) (u : Word) :
    Prop :=
  ∃ us : Fin R.cmds.length → Word, (∀ i, CmdCode (R.cmds.get i) (us i)) ∧
    u = integerCode s ++ integerCode ℓ ++ integerCode R.w ++ integerCode R.accept.val ++
      integerCode R.reject.val ++ integerCode R.cmds.length ++ (List.ofFn us).flatten ++
      integerCode p.val ++ valCode a

end Supplement

end ImplicitParityWL


