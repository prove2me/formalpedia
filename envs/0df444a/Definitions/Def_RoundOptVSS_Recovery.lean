-- Prove2me | Definitions.Def_RoundOptVSS_Recovery
-- name    : RoundOptVSS_Recovery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:00:43.940092+00:00
-- url     : https://prove2.me/theorems/8ade8812-2478-4c7f-98d7-ebfd08e0345e
-- title:
--   Key recovery of the VSS compiler: $\mathrm{Key}$, $\mathcal K(Z,c)$, $\Phi$ and the local computation of Protocol 9
-- statement:
--   Let $m$ be the mask length and $\lambda\in\mathbb E$. Each party $P_j$ has a deposit $C_j\in\mathbb E^m$ (or a malformed one). An **assignment** gives every party a vector in $\mathbb E^m$ or `bad`. Put $\mathrm{Key}(C,r)=C-\lambda r$ for $C,r\in\mathbb E^m$ and `bad` otherwise, $D_j=\mathbb E^m\cup\{\mathrm{bad}\}$ if $C_j$ is well formed and $\{\mathrm{bad}\}$ otherwise, and for $Z\subseteq[n]$ and a vector $c$
--
--   $$\mathcal K(Z,c)=\Big\{k\in\prod_jD_j:\ k_j=c_j\text{ for }j\notin Z\Big\}.$$
--
--   Given the decoders $D_{a,i}$ of the mask instances at a party $P_i$ and its searches $\mathrm{Search}_a(Z,c,b)$, $b\in\{\mathrm{rej},\mathrm{acc}\}$, the **local computation of Protocol 9** with announced masks $\hat R$ is: (1) with $k^{raw}_j=\mathrm{Key}(C_j,\hat R_j)$, cache every $j$ with $r=D_{j,i}(k^{raw})\ne\bot$, setting $c_j=\mathrm{Key}(C_j,r)$, and let $U$ be the uncached indices; (2) set $Z=U$ and repeatedly add the first $a\notin Z$ (in increasing order) with $\mathrm{Search}_a(Z,c,\mathrm{rej})\ne\mathrm{none}$; (3) for each $a\in U$ in increasing order, if $k=\mathrm{Search}_a(Z,c,\mathrm{acc})\ne\mathrm{none}$ and $r=D_{a,i}(k)\ne\bot$, cache $a$ with $c_a=\mathrm{Key}(C_a,r)$; (4) if $U$ changed, return to (2); otherwise output $k^\star$, which is `bad` on $Z$ and $c$ elsewhere.
--
--   For a vector $c$ and decoders $D_a$ the map $\Phi(Z)=Z\cup\{a:\exists k\in\mathcal K(Z,c),\ D_a(k)=\bot\}$ is the one of the proof of Lemma 8.4.
--
--   **Formalization Note** Both loops carry explicit fuel $n+1$, which is never exhausted (each restart follows a strict growth of the cache). The decoders and searches are parameters: they already contain the party's sharing states and the openings.
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), §8.2 notation and Protocol 9 (pp.27–28), proof of Lemma 8.4 (pp.29–30)

import Mathlib

open Classical

namespace RoundOptVSS

/-!
# Key recovery of the VSS compiler (§8.2, Protocol 9)

Liu-Zhang, Masserova, *Round-Optimal Statistical Verifiable Secret Sharing with Polynomial
Complexity*, manuscript (STOC 2027 submission, sha256 3a45d95d…), §8.2 (pp.27–28): `Key(C, r)`,
the domains `D_j`, the sets `𝒦(Z, c)`, the lifted searches `Search_a(Z, c, b)` and the local
computation of Protocol 9; §8.3 (p.29): the canonical vector `c_j = Key(C_j, ρ_j)`,
honest-consistency, and the map `Φ(Z) = Z ∪ {a : ∃ k ∈ 𝒦(Z, c), D_{a,i}(k) = ⊥}`.

**Formalization Note.**
* An assignment is `Fin n → Option (Fin m → 𝔼)` (`none` = bad); the deposits `C_j` are
  `Option (Fin m → 𝔼)` (`none` = malformed), and so are the announced masks `R̂_j`.
* The decoders `D_{a,i}` of the mask instances (`a ∈ [n]`, output in `𝔼^m`) and the lifted
  searches `Search_a` of the decoding party are parameters of the local computation; they already
  include the party's states and the actual openings.
* Protocol 9's loops are bounded: the closure scan restarts at most `n + 1` times and the passes
  are at most `n + 1` (each restart follows a strict growth of the cache, p.28); the fallback
  branches after the fuel runs out are never reached.
-/

variable {𝔼 : Type} [Field 𝔼] {n m : ℕ}

/-- An assignment `k = (k_1, …, k_n)`, `k_j ∈ 𝔼^m ∪ {bad}` (`bad` = `none`). -/
abbrev KeyAssign (𝔼 : Type) (n m : ℕ) := Fin n → Option (Fin m → 𝔼)

/-- `Key(C, r) = C − λ r` for `C, r ∈ 𝔼^m`, and bad otherwise. -/
noncomputable def keyOf (lam : 𝔼) (Cj r : Option (Fin m → 𝔼)) : Option (Fin m → 𝔼) :=
  match Cj, r with
  | some C, some r => some (C - lam • r)
  | _, _ => none

/-- `𝒦(Z, c) = {k ∈ ∏_j D_j : k_j = c_j for j ∉ Z}`, where `D_j = 𝔼^m ∪ {bad}` if `C_j` is well
formed and `{bad}` otherwise. -/
def KSet (Cdep : Fin n → Option (Fin m → 𝔼)) (Z : Finset (Fin n)) (c : KeyAssign 𝔼 n m) :
    Set (KeyAssign 𝔼 n m) :=
  {k | (∀ j, Cdep j = none → k j = none) ∧ ∀ j, j ∉ Z → k j = c j}

/-- The search mode `b ∈ {rej, acc}`. -/
inductive SearchMode where
  | rej
  | acc

/-- `k⋆`: bad on `Z` and `c` elsewhere. -/
noncomputable def starOf (Z : Finset (Fin n)) (c : KeyAssign 𝔼 n m) : KeyAssign 𝔼 n m :=
  fun j => if j ∈ Z then none else c j

section Protocol9

variable (lam : 𝔼) (Cdep : Fin n → Option (Fin m → 𝔼))
  (Dm : Fin n → KeyAssign 𝔼 n m → Option (Fin m → 𝔼))
  (Srch : Fin n → Finset (Fin n) → KeyAssign 𝔼 n m → SearchMode → Option (KeyAssign 𝔼 n m))

/-- Step 1 (Initialize) at the decoding party, from the announced masks `R̂`: with
`k^raw_j = Key(C_j, R̂_j)`, every `j` with `r = D_{j,i}(k^raw) ≠ ⊥` is cached, `c_j = Key(C_j, r)`
and removed from `U`. Returns `(U, c)` (`c_j` for `j ∈ U` is unused and set to bad). -/
noncomputable def p9Init (Rhat : Fin n → Option (Fin m → 𝔼)) : Finset (Fin n) × KeyAssign 𝔼 n m :=
  (Finset.univ.filter fun j => Dm j (fun l => keyOf lam (Cdep l) (Rhat l)) = none,
   fun j =>
     match Dm j (fun l => keyOf lam (Cdep l) (Rhat l)) with
     | some r => keyOf lam (Cdep j) (some r)
     | none => none)

/-- Step 2 (Close): scan `a ∉ Z` in increasing order; the first `a` with
`Search_a(Z, c, rej) ≠ none` is added and the scan restarts; stop after a scan that adds
nothing. -/
noncomputable def closeLoop (c : KeyAssign 𝔼 n m) : ℕ → Finset (Fin n) → Finset (Fin n)
  | 0, Z => Z
  | f + 1, Z =>
    match (List.finRange n).find? (fun a => decide (a ∉ Z ∧ (Srch a Z c .rej).isSome)) with
    | some a => closeLoop c f (insert a Z)
    | none => Z

/-- One step of step 3 (Recover) for `a`: if `k = Search_a(Z, c, acc) ≠ none` and
`r = D_{a,i}(k) ≠ ⊥`, cache `a`: `c_a = Key(C_a, r)` and remove `a` from `U`. -/
noncomputable def recoverStep (Z : Finset (Fin n)) (s : Finset (Fin n) × KeyAssign 𝔼 n m) (a : Fin n) :
    Finset (Fin n) × KeyAssign 𝔼 n m :=
  match Srch a Z s.2 .acc with
  | some k =>
    match Dm a k with
    | some r => (s.1.erase a, Function.update s.2 a (keyOf lam (Cdep a) (some r)))
    | none => s
  | none => s

/-- Step 3 (Recover): for each `a ∈ U_old` in increasing order (`Z` fixed). -/
noncomputable def recoverAll (Z : Finset (Fin n)) (s : Finset (Fin n) × KeyAssign 𝔼 n m) :
    Finset (Fin n) × KeyAssign 𝔼 n m :=
  ((List.finRange n).filter fun a => decide (a ∈ s.1)).foldl
    (recoverStep lam Cdep Dm Srch Z) s

/-- Steps 2–4 with at most `f` passes: close from `Z = U`, recover, and either restart (if `U`
changed) or return `k⋆` (bad on `Z`, `c` elsewhere). -/
noncomputable def p9Loop : ℕ → Finset (Fin n) × KeyAssign 𝔼 n m → KeyAssign 𝔼 n m
  | 0, s => starOf (closeLoop Srch s.2 (n + 1) s.1) s.2
  | f + 1, s =>
    let Z := closeLoop Srch s.2 (n + 1) s.1
    let s' := recoverAll lam Cdep Dm Srch Z s
    if s'.1 = s.1 then starOf Z s.2 else p9Loop f s'

/-- The assignment `k⋆` that Protocol 9's local computation produces at the decoding party from
the announced masks `R̂`. -/
noncomputable def protocol9Assign (Rhat : Fin n → Option (Fin m → 𝔼)) : KeyAssign 𝔼 n m :=
  p9Loop lam Cdep Dm Srch (n + 1) (p9Init lam Cdep Dm Rhat)

end Protocol9

/-- `Φ(Z) = Z ∪ {a : ∃ k ∈ 𝒦(Z, c), D_{a,i}(k) = ⊥}` for decoders `Dm` (instance `a`). -/
noncomputable def Phi (Cdep : Fin n → Option (Fin m → 𝔼)) (c : KeyAssign 𝔼 n m)
    (Dm : Fin n → KeyAssign 𝔼 n m → Option (Fin m → 𝔼)) (Z : Finset (Fin n)) :
    Finset (Fin n) :=
  Z ∪ Finset.univ.filter fun a => ∃ k ∈ KSet Cdep Z c, Dm a k = none

/-- `Z` is the least fixed point of `Φ`. -/
def IsLeastFixedPoint (Φ : Finset (Fin n) → Finset (Fin n)) (Z : Finset (Fin n)) : Prop :=
  Φ Z = Z ∧ ∀ Z', Φ Z' = Z' → Z ⊆ Z'

end RoundOptVSS


