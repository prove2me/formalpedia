-- Prove2me | Definitions.Def_NKtLB_NondetOutputs
-- name    : NKtLB_NondetOutputs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:59:50.423089+00:00
-- url     : https://prove2.me/theorems/d85e0bf8-424a-4890-a6e0-1a663b81b8ee
-- title:
--   Nondeterministic output of a program
-- statement:
--   A program $\Pi$ **nondeterministically outputs** $x$ on $(y;r)$ in time $t$, with oracle $O$ and queries of length at most $\ell$, if
--
--   1. for every guess $w\in\{0,1\}^t$, $U$ run on $\Pi$ with auxiliary string $y$, guess $w$ and random string $r$ halts within $t$ steps with output $x$ or $\bot$, making only queries of length at most $\ell$; and
--   2. for some guess $w\in\{0,1\}^t$ it halts within $t$ steps with output $x$.
--
--   Both halves matter. Without the first, one program would describe every string; the second makes the program describe $x$.
--
--   **Formalization Note** "Outputs $\bot$" means the output is the one-symbol word $\bot$; a run that does not halt within $t$ steps outputs neither. $\ell=\infty$ is the unrestricted oracle $O$, a finite $\ell$ is $O^{\le\ell}$, and the oracle $\emptyset$ gives the unrelativized notion. Because the guess tape is read sequentially, a run of at most $t$ steps never reads past the first $t$ guess bits.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.2–3.3, pp.21–22

import Mathlib
import Definitions.Def_NKtLB_Machine

namespace NKtLB

/-- **Nondeterministic output** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §3.2, pp.21–22): "We say that a program `Π`
non-deterministically outputs `y` on input `(x; r)` in time `t` if:
• `∀w ∈ {0,1}^t`, `Π(x; w; r)` outputs either `y` or `⊥` in time `t`, and
• `∃w ∈ {0,1}^t`, `Π(x; w; r)` outputs `y` in time `t`."
Here (§3.3, p.22) "a program `Π` outputs `x` in `t` steps" means that `U(Π) = x` when `U` runs for
at most `t` steps on input `Π`.

`NondetOutputs U O ℓ p y r t x`: for every guess `w` of length exactly `t`, the universal machine
`U` with `p` on its input tape, `y` on the auxiliary tape, `w` on the guess tape and `r` on the
randomness tape, with oracle `O`, halts within `t` steps with output `x` or `⊥` and makes only
queries of length at most `ℓ` in those steps; and for some such guess it halts with output `x`.

**Formalization Note.** "Outputs `⊥`" is the one-symbol output word `⊥`; a run that does not halt
within `t` steps outputs neither. `ℓ = ⊤` is the unrestricted oracle `O`, a finite `ℓ` is `O^{≤ℓ}`
("restricting query length to at most `ℓ`", Lemma 45, p.30), the oracle `∅` is the unrelativized
notion. -/
def NondetOutputs (U : Machine) (O : Set (List Bool)) (ℓ : ℕ∞) (p y r : List Bool) (t : ℕ)
    (x : List Bool) : Prop :=
  (∀ w : List Bool, w.length = t → U.QueryBounded O ℓ ⟨p, y, w, r⟩ t ∧
      (U.HaltsWith O ⟨p, y, w, r⟩ t (bitsSym x) ∨ U.HaltsWith O ⟨p, y, w, r⟩ t [Sym.bot])) ∧
    ∃ w : List Bool, w.length = t ∧ U.HaltsWith O ⟨p, y, w, r⟩ t (bitsSym x)

end NKtLB


