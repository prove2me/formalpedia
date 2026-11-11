-- Prove2me | Definitions.Def_OptimalXOR_Total_Compositions
-- name    : OptimalXOR_Total_Compositions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:06:12.999221+00:00
-- url     : https://prove2.me/theorems/20c0afe0-7755-49bb-ba1c-b31f9dc85fab
-- title:
--   Conditional composition $\pi'$ (Proposition 2.4) and independent executions (Lemma 2.5)
-- statement:
--   Two constructions of protocols from protocols.
--
--   1. **Conditional composition** (Proposition 2.4). Given protocols $\pi,\rho$ on $\mathcal X\times\mathcal Y$ with output set $\mathcal Z$ and a set $\mathcal M$ of transcripts of $\pi$, the protocol $\pi'$ runs $\pi$ and then, if the transcript of $\pi$ lies in $\mathcal M$, runs $\rho$ on the same input with fresh public and private randomness. The output of $\pi'$ is that of $\rho$ if $\rho$ is run, and that of $\pi$ otherwise.
--   2. **Independent executions** (Lemma 2.5). Given protocols $\pi_1,\dots,\pi_t$, with $\pi_i$ on $\mathcal X_i\times\mathcal Y_i$, and maps $x\mapsto x^{(i)}\in\mathcal X_i$, $y\mapsto y^{(i)}\in\mathcal Y_i$, the protocol $\pi$ on $\mathcal X\times\mathcal Y$ runs $\pi_1,\dots,\pi_t$ one after the other, run $i$ on $(x^{(i)},y^{(i)})$, with independent public and private randomness, every message of run $i$ depending only on the sender's input to run $i$, the tapes of run $i$ and the messages of run $i$. With identity maps this is "running them on a common input"; with coordinate projections of $\mathcal X=\prod_i\mathcal X_i$, $\mathcal Y=\prod_i\mathcal Y_i$ it is "$\pi_i$ runs on the $i$-th coordinate pair". The output of $\pi$ is an arbitrary given measurable map of Bob's input, the public tapes, Bob's private tapes and the transcript.
--
--   These are the protocols to which Proposition 2.4 and Lemma 2.5 apply.
--
--   **Formalization Note** On the published fixed-tree protocols, $\pi'$ has the tree of $\pi$ with the tree of $\rho$ grafted at exactly those leaves whose message history lies in $\mathcal M$ (`treeGraft`); its tapes are the products of those of $\pi$ and $\rho$ (`sourceProd`), and `treeSplit` recovers the history of $\rho$. `indepRun` concatenates the trees (`treeConcat`), uses product tapes (`sourcePi`), and `treeLocate` finds the run in progress and its local history. A transcript is a message history `List Bool`.
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), pp. 16–17 (PDF 18–19), Proposition 2.4 and Lemma 2.5

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol

open MeasureTheory

namespace OptimalXOR.Total

open CaiZhuInfo.Matrix

/-! Sherstov, *Optimal XOR Lemmas for Information Complexity*, STOC 2027 submission, §2.5,
printed pp. 16–17 / PDF pp. 18–19: protocol compositions on the published
`CaiZhuInfo.Matrix.Protocol`.

* `condCompose π ρ ℳ` is the protocol `π′` of Proposition 2.4: run `π`, then, if the transcript
  (message history) of `π` lies in `ℳ`, run `ρ` on the same input with fresh public and private
  randomness; output `ρ`'s answer if `ρ` was run and `π`'s otherwise. In the fixed-tree model this
  is the tree of `π` with the tree of `ρ` grafted at exactly the leaves whose history lies in `ℳ`.
* `indepRun π fA fB out` runs the protocols `π 0, …, π (t−1)` one after the other, protocol `i` on
  the input `(fA i x, fB i y)`, with independent public and private tapes, each run using only its
  own tapes and its own messages (Lemma 2.5). The final output map `out` is arbitrary. -/

noncomputable section

/-- Two independent random sources, jointly. -/
def sourceProd (S T : RandomSource) : RandomSource where
  Carrier := S.Carrier × T.Carrier
  measurable := inferInstance
  law := S.law.prod T.law
  probability := inferInstance

/-- Finitely many independent random sources, jointly. -/
def sourcePi {t : ℕ} (S : Fin t → RandomSource) : RandomSource where
  Carrier := ∀ i, (S i).Carrier
  measurable := inferInstance
  law := Measure.pi (fun i => (S i).law)
  probability := inferInstance

/-- Walk the history `h` down the tree. If it passes a leaf after consuming the prefix `pre`,
return `some (pre, rest)`; if `h` ends at an internal node, return `none`. -/
def treeSplit : CommunicationTree → List Bool → Option (List Bool × List Bool)
  | .leaf, h => some ([], h)
  | .alice _ _, [] => none
  | .alice t0 _, false :: h => (treeSplit t0 h).map (fun q => (false :: q.1, q.2))
  | .alice _ t1, true :: h => (treeSplit t1 h).map (fun q => (true :: q.1, q.2))
  | .bob _ _, [] => none
  | .bob t0 _, false :: h => (treeSplit t0 h).map (fun q => (false :: q.1, q.2))
  | .bob _ t1, true :: h => (treeSplit t1 h).map (fun q => (true :: q.1, q.2))

open scoped Classical in
/-- Replace each leaf of a tree, reached by the history `p`, by `s` if `p ∈ ℳ`, and keep it a leaf
otherwise. The argument `p` is the history leading to the current node. -/
def treeGraft (ℳ : Set (List Bool)) (s : CommunicationTree) :
    CommunicationTree → List Bool → CommunicationTree
  | .leaf, p => if p ∈ ℳ then s else .leaf
  | .alice t0 t1, p => .alice (treeGraft ℳ s t0 (p ++ [false])) (treeGraft ℳ s t1 (p ++ [true]))
  | .bob t0 t1, p => .bob (treeGraft ℳ s t0 (p ++ [false])) (treeGraft ℳ s t1 (p ++ [true]))

/-- Replace every leaf of the first tree by the second tree. -/
def treeAppend : CommunicationTree → CommunicationTree → CommunicationTree
  | .leaf, s => s
  | .alice t0 t1, s => .alice (treeAppend t0 s) (treeAppend t1 s)
  | .bob t0 t1, s => .bob (treeAppend t0 s) (treeAppend t1 s)

/-- The trees `T 0, T 1, …, T (t−1)` run one after the other. -/
def treeConcat : (t : ℕ) → (Fin t → CommunicationTree) → CommunicationTree
  | 0, _ => .leaf
  | t + 1, T => treeAppend (T 0) (treeConcat t (fun i => T i.succ))

/-- For a history `h` of the concatenated tree ending at an internal node: the index `i` of the
run in progress and the history of run `i` so far. -/
def treeLocate :
    (t : ℕ) → (Fin t → CommunicationTree) → List Bool → Option (Fin t × List Bool)
  | 0, _, _ => none
  | t + 1, T, h =>
    match treeSplit (T 0) h with
    | none => some (0, h)
    | some q => (treeLocate t (fun i => T i.succ) q.2).map
        (fun r => (r.1.succ, r.2))


variable {X Y Z : Type}

open scoped Classical in
/-- The protocol `π′` of Proposition 2.4 (conditional composition): run `π`; if the transcript
of `π` lies in `ℳ`, run `ρ` on the same input with fresh public and private randomness.
The output is that of `ρ` if `ρ` is run, and that of `π` otherwise. -/
def condCompose (π ρ : Protocol X Y Z) (ℳ : Set (List Bool)) : Protocol X Y Z where
  shared := sourceProd π.shared ρ.shared
  privateA := sourceProd π.privateA ρ.privateA
  privateB := sourceProd π.privateB ρ.privateB
  tree := treeGraft ℳ ρ.tree π.tree []
  sendA x r a h :=
    match treeSplit π.tree h with
    | none => π.sendA x r.1 a.1 h
    | some q => ρ.sendA x r.2 a.2 q.2
  sendB y r b h :=
    match treeSplit π.tree h with
    | none => π.sendB y r.1 b.1 h
    | some q => ρ.sendB y r.2 b.2 q.2
  out y r b h :=
    match treeSplit π.tree h with
    | none => π.out y r.1 b.1 h
    | some q => if q.1 ∈ ℳ then ρ.out y r.2 b.2 q.2 else π.out y r.1 b.1 q.1
  sendA_measurable x h := by
    rcases treeSplit π.tree h with _ | q
    · exact (π.sendA_measurable x h).comp (measurable_fst.fst.prodMk measurable_snd.fst)
    · exact (ρ.sendA_measurable x q.2).comp (measurable_fst.snd.prodMk measurable_snd.snd)
  sendB_measurable y h := by
    rcases treeSplit π.tree h with _ | q
    · exact (π.sendB_measurable y h).comp (measurable_fst.fst.prodMk measurable_snd.fst)
    · exact (ρ.sendB_measurable y q.2).comp (measurable_fst.snd.prodMk measurable_snd.snd)
  out_measurable y h := by
    rcases treeSplit π.tree h with _ | q
    · exact (π.out_measurable y h).comp (measurable_fst.fst.prodMk measurable_snd.fst)
    · dsimp only
      split_ifs
      · exact (ρ.out_measurable y q.2).comp (measurable_fst.snd.prodMk measurable_snd.snd)
      · exact (π.out_measurable y q.1).comp (measurable_fst.fst.prodMk measurable_snd.fst)

/-- Independent executions (Lemma 2.5): the protocols `π 0, …, π (t−1)` run one after the other
with independent public and private tapes, run `i` on the input `(fA i x, fB i y)`, each message
of run `i` depending only on the sender's input to run `i`, run `i`'s tapes and the messages of
run `i`. The output map `out` (of Bob's input, all public and Bob's private tapes, and the whole
history) is arbitrary: the information cost does not depend on it. -/
def indepRun {t : ℕ} {Xs Ys Zs : Fin t → Type} (π : ∀ i, Protocol (Xs i) (Ys i) (Zs i))
    (fA : ∀ i, X → Xs i) (fB : ∀ i, Y → Ys i)
    (out : Y → (∀ i, (π i).shared.Carrier) → (∀ i, (π i).privateB.Carrier) → List Bool → Z)
    (hout : ∀ y h, @Measurable ((∀ i, (π i).shared.Carrier) × (∀ i, (π i).privateB.Carrier)) Z
      inferInstance ⊤ (fun u => out y u.1 u.2 h)) :
    Protocol X Y Z where
  shared := sourcePi (fun i => (π i).shared)
  privateA := sourcePi (fun i => (π i).privateA)
  privateB := sourcePi (fun i => (π i).privateB)
  tree := treeConcat t (fun i => (π i).tree)
  sendA x r a h :=
    match treeLocate t (fun i => (π i).tree) h with
    | none => false
    | some q => (π q.1).sendA (fA q.1 x) (r q.1) (a q.1) q.2
  sendB y r b h :=
    match treeLocate t (fun i => (π i).tree) h with
    | none => false
    | some q => (π q.1).sendB (fB q.1 y) (r q.1) (b q.1) q.2
  out := out
  sendA_measurable x h := by
    rcases treeLocate t (fun i => (π i).tree) h with _ | q
    · exact measurable_const
    · have hm : Measurable (fun u : (sourcePi (fun i => (π i).shared)).Carrier ×
          (sourcePi (fun i => (π i).privateA)).Carrier => (u.1 q.1, u.2 q.1)) :=
        ((measurable_pi_apply q.1).comp measurable_fst).prodMk
          ((measurable_pi_apply q.1).comp measurable_snd)
      exact ((π q.1).sendA_measurable (fA q.1 x) q.2).comp hm
  sendB_measurable y h := by
    rcases treeLocate t (fun i => (π i).tree) h with _ | q
    · exact measurable_const
    · have hm : Measurable (fun u : (sourcePi (fun i => (π i).shared)).Carrier ×
          (sourcePi (fun i => (π i).privateB)).Carrier => (u.1 q.1, u.2 q.1)) :=
        ((measurable_pi_apply q.1).comp measurable_fst).prodMk
          ((measurable_pi_apply q.1).comp measurable_snd)
      exact ((π q.1).sendB_measurable (fB q.1 y) q.2).comp hm
  out_measurable := hout


end

end OptimalXOR.Total


