-- Prove2me | Definitions.Def_DQILocal_Recon_TreeCode
-- name    : DQILocal_Recon_TreeCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:18.000322+00:00
-- url     : https://prove2.me/theorems/ef93a53f-d07f-4299-9909-8fa079e6a382
-- title:
--   The $(k,D)$ tree $\mathcal T_t$, its tree code $C_t$, the optimal root success, and tree isomorphisms of a ball
-- statement:
--   $\mathcal T_t$ is the $(k,D)$ tree of depth $t$ rooted at a symbol: the root has $k$ child checks, every check has $D-1$ child symbols, every non-root symbol at depth less than $t$ has $k-1$ child checks, and the symbols at depth $t$, measured in check layers, are the leaves. The **tree code** $C_t$ is the set of assignments of values in $\mathbb Z_q$ to the symbols of $\mathcal T_t$ that satisfy every check; no other constraint acts on the leaves.
--
--   For a POVM $\{E_y\}$ on the qudits of $\mathcal T_t$, its success for the root is
--
--   $$\frac1{|C_t|}\sum_{y\in C_t}\Bigl\langle\textstyle\bigotimes_v\psi^p_{y_v}\Bigr|E_{y_{\mathrm{root}}}\Bigl|\textstyle\bigotimes_v\psi^p_{y_v}\Bigr\rangle ,$$
--
--   and `treeOpt` is its supremum over **all** POVMs: the largest probability, over all measurements, of outputting the root value.
--
--   A **tree isomorphism** of the ball around $i$ is a pair of bijections from the symbols of $\mathcal T_t$ onto $N_t(i)$ and from the checks of $\mathcal T_t$ onto $F_t(i)$ that preserves adjacency and non-adjacency and sends the root to $i$; a POVM on $\mathcal T_t$ is transported along it to a POVM on the qudits of $N_t(i)$.
--
--   **Formalization Note** Vertices are index paths: the root is the empty list, the child checks of a symbol $v$ at depth $d$ are $v\,a$ with $a<k$ at the root and $a<k-1$ elsewhere, and the child symbols of a check $c$ are $c\,b$ with $b<D-1$. `treeOpt` is defined independently of $P_t$ and of BPQM.
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), §4.2 and Proposition 4.3, p. 24; p. 30 ("By LT_t(i), C_t(i) is the tree code C_t")

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Decoder

namespace DQILocal.Recon

open scoped BigOperators

/-- **The `(k, D)` tree `T_t` and its tree code `C_t`.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), §4.2, p. 24: "Let `T_t`
be the `(k, D)` tree of depth `t` rooted at a symbol. The root has `k` child checks, every check has
`D - 1` child symbols, every non-root symbol at depth less than `t` has `k - 1` child checks, and the
symbols at depth `t`, measured in check layers, are the leaves."

Vertices are index paths (`List ℕ`): the root symbol is `[]`; the children checks of a symbol `v`
at depth `d` are `v ++ [a]` with `a < branchT k d` (`k` at the root, `k - 1` elsewhere); the children
symbols of a check `c` are `c ++ [b]` with `b < D - 1`. So a symbol at depth `d` is a path of length
`2d` and a check is a path of odd length.

`branchT k d` is the number of child checks of a symbol at depth `d`. -/
def branchT (k d : ℕ) : ℕ := if d = 0 then k else k - 1

/-- The symbols of `T_t` at depth `d` (`d` check layers below the root). -/
def symLayer (k D : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | d + 1 => (symLayer k D d).biUnion fun v =>
      ((Finset.range (branchT k d)) ×ˢ (Finset.range (D - 1))).image fun ab => v ++ [ab.1, ab.2]

/-- The checks that are children of the symbols at depth `d`. -/
def chkLayer (k D d : ℕ) : Finset (List ℕ) :=
  (symLayer k D d).biUnion fun v => (Finset.range (branchT k d)).image fun a => v ++ [a]

/-- The symbols of `T_t` (depths `0, …, t`). -/
def treeSyms (k D t : ℕ) : Finset (List ℕ) := (Finset.range (t + 1)).biUnion (symLayer k D)

/-- The checks of `T_t` (children of the symbols at depths `0, …, t - 1`). -/
def treeChks (k D t : ℕ) : Finset (List ℕ) := (Finset.range t).biUnion (chkLayer k D)

/-- Adjacency in `T_t`: a symbol `s` and a check `c` are adjacent when `c` is a child of `s`
(`c = s ++ [a]`) or `s` is a child of `c` (`s = c ++ [b]`). -/
def treeAdj (s c : List ℕ) : Prop := (∃ a : ℕ, c = s ++ [a]) ∨ (∃ b : ℕ, s = c ++ [b])

/-- The root symbol of `T_t`. -/
def treeRoot (k D t : ℕ) : treeSyms k D t :=
  ⟨[], by simp only [treeSyms, Finset.mem_biUnion, Finset.mem_range]; exact ⟨0, Nat.succ_pos t, by simp [symLayer]⟩⟩

/-- **The tree code `C_t` (§4.2, p. 24)**: the assignments of values in `ℤ_q` to the symbols of
`T_t` that satisfy every check (the values of the symbols adjacent to a check sum to `0`). No other
constraint acts on the leaves. -/
noncomputable def treeCodeT (q : ℕ) [NeZero q] (k D t : ℕ) : Finset (treeSyms k D t → ZMod q) := by
  classical
  exact Finset.univ.filter fun y => ∀ c ∈ treeChks k D t,
    ∑ s : treeSyms k D t, (if treeAdj s.1 c then y s else 0) = 0

/-- The success probability of a POVM `E` on the qudits of `T_t` (outcomes in `ℤ_q`) for the root:
`y` uniform on `C_t`, the state `⊗_{v ∈ T_t} |ψ^p_{y_v}⟩`, success when the outcome is `y_root`
(Proposition 4.3, p. 24). -/
noncomputable def treeSuccess {q : ℕ} [NeZero q] (k D t : ℕ) (p : ZMod q → ℝ)
    (E : ZMod q → Matrix (treeSyms k D t → ZMod q) (treeSyms k D t → ZMod q) ℂ) : ℝ :=
  (1 / ((treeCodeT q k D t).card : ℝ)) *
    ∑ y ∈ treeCodeT q k D t, expectVal (E (y (treeRoot k D t))) (psiProd p y)

/-- **The optimal success probability for the root of `T_t`** (Proposition 4.3, p. 24): the
supremum of `treeSuccess` over **all** POVMs on the qudits of `T_t` with outcomes in `ℤ_q`.

**Formalization Note.** Defined independently of `P_t` and of BPQM. The set is nonempty and bounded
above by one, so `sSup` is the true supremum. -/
noncomputable def treeOpt (q : ℕ) [NeZero q] (k D t : ℕ) (p : ZMod q → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ E : ZMod q → Matrix (treeSyms k D t → ZMod q) (treeSyms k D t → ZMod q) ℂ,
    IsPOVM E ∧ r = treeSuccess k D t p E}

/-- **An isomorphism of the ball of radius `2t` around `i` with `T_t`** (p. 30: "By `LT_t(i)`,
`C_t(i)` is the tree code `C_t`"): bijections from the symbols of `T_t` onto `N_t(i)` and from the
checks of `T_t` onto `F_t(i)` that preserve adjacency and non-adjacency and send the root to `i`. -/
structure TreeIso {m : ℕ} {κ : Type} [Fintype κ] (k D : ℕ) (B : Matrix (Fin m) κ Bool) (i : Fin m)
    (t : ℕ) where
  /-- The symbol bijection. -/
  sym : treeSyms k D t ≃ ballSym B i t
  /-- The check bijection. -/
  chk : treeChks k D t ≃ ballChk B i t
  /-- The root goes to `i`. -/
  root : (sym (treeRoot k D t)).1 = i
  /-- Adjacency is preserved and reflected. -/
  adj : ∀ s c, treeAdj s.1 c.1 ↔ B (sym s).1 (chk c).1 = true

/-- A POVM on the qudits of `T_t` transported to the qudits of `N_t(i)` along a tree isomorphism. -/
def TreeIso.transport {q : ℕ} {m : ℕ} {κ : Type} [Fintype κ] {k D : ℕ}
    {B : Matrix (Fin m) κ Bool} {i : Fin m} {t : ℕ} (φ : TreeIso k D B i t)
    (E : ZMod q → Matrix (treeSyms k D t → ZMod q) (treeSyms k D t → ZMod q) ℂ) :
    ZMod q → Matrix (ballSym B i t → ZMod q) (ballSym B i t → ZMod q) ℂ :=
  fun y => Matrix.reindex (φ.sym.arrowCongr (Equiv.refl (ZMod q)))
    (φ.sym.arrowCongr (Equiv.refl (ZMod q))) (E y)

end DQILocal.Recon


