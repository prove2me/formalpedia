-- Prove2me | Definitions.Def_QAlgorithms_Defs_Learning
-- name    : QAlgorithms_Defs_Learning
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:52:56.885019+00:00
-- url     : https://prove2.me/theorems/3cb36e04-185c-4757-b482-1d72110b2953
-- title:
--   Learning models: exact, PAC and agnostic learning from classical or quantum data
-- statement:
--   Learning models: exact, PAC and agnostic learning from classical or quantum data
--
--   ### QAlgorithms.Learning.IsDistribution
--
--   For a finite type $X$ and a real function $D$ on $X$, $\mathrm{IsDistribution}(D)$ holds exactly when both of the following are true:
--
--   - $D(x) \ge 0$ for every $x \in X$;
--   - $\sum_{x\in X} D(x) = 1$.
--
--   If $X$ is empty the sum is $0$, so the predicate is unsatisfiable.
--
--   ### QAlgorithms.Learning.uniformDist
--
--   For a finite type $X$, this defines the function $u_X : X \to \mathbb{R}$ that is constant:
--
--   $$u_X(x) = \frac{1}{|X|} \quad \text{for every } x \in X.$$
--
--   When $X$ is empty, the formula would read $1/0$, which the code evaluates to $0$. This case is vacuous, since there are no points to evaluate at.
--
--   ### QAlgorithms.Learning.pacError
--
--   Let $X$ be a finite type, $D : X \to \mathbb{R}$ an arbitrary real-valued function, and $c, h : X \to \{0,1\}$ two Boolean functions (a target concept and a hypothesis). The definition is the total $D$-weight of the points where $h$ and $c$ disagree:
--
--   $$\mathrm{err}_D(c,h) = \sum_{x \in X,\; h(x) \neq c(x)} D(x).$$
--
--   $D$ is not required to be nonnegative or to sum to $1$. If $h = c$, the sum is empty and the value is $0$.
--
--   ### QAlgorithms.Learning.agnosticError
--
--   Let $X$ be a finite type, $D : X \times \{0,1\} \to \mathbb{R}$ an arbitrary real-valued function on labelled examples, and $h : X \to \{0,1\}$ a hypothesis. The definition is the total $D$-weight of the labelled pairs that $h$ mislabels:
--
--   $$\mathrm{err}_D(h) = \sum_{(x,b) \in X \times \{0,1\},\; h(x) \neq b} D(x,b).$$
--
--   No nonnegativity or normalization of $D$ is assumed.
--
--   ### QAlgorithms.Learning.optError
--
--   Let $X$ be a finite type, $D : X \times \{0,1\} \to \mathbb{R}$ arbitrary, and $C$ a finite set of Boolean functions $X \to \{0,1\}$ (a concept class). The definition is the infimum of the agnostic error over the class:
--
--   $$\mathrm{opt}_D(C) = \inf_{c \in C} \mathrm{err}_D(c), \qquad \mathrm{err}_D(c) = \sum_{(x,b):\, c(x) \neq b} D(x,b).$$
--
--   When $C$ is nonempty this is a minimum over finitely many values. When $C$ is empty, the infimum over the empty index set is taken by the code to be $0$, not $+\infty$.
--
--   ### QAlgorithms.Learning.vcDimClass
--
--   Let $X$ be a finite type with decidable equality and $C$ a finite set of Boolean functions on $X$. Identify each $c \in C$ with its support $\{x : c(x) = 1\} \subseteq X$, and let $\mathcal{A} = \{\{x : c(x)=1\} : c \in C\}$ be the resulting finite family of subsets of $X$.
--
--   The definition returns the VC dimension of $\mathcal{A}$: the largest cardinality of a set $S \subseteq X$ that is shattered by $\mathcal{A}$. Here $S$ is shattered if for every $T \subseteq S$ there is $A \in \mathcal{A}$ with $S \cap A = T$.
--
--   If $C$ is empty, no set (not even $\varnothing$) is shattered, and the value is $0$. If $C$ has a single element, only $\varnothing$ is shattered, and the value is again $0$.
--
--   ### QAlgorithms.Learning.IsNontrivialClass
--
--   For a finite type $X$ with decidable equality and a finite set $C$ of Boolean functions on $X$, the predicate says that both of the following hold:
--
--   1. $|C| \ge 2$;
--   2. there is no function $c : X \to \{0,1\}$ such that $C$ equals exactly the set $\{c, \bar c\}$, where $\bar c(x) = \neg c(x)$ is the pointwise complement.
--
--   If $X$ is empty, there is only one function on $X$. Condition (1) then cannot hold, so the predicate is false.
--
--   ### QAlgorithms.Learning.exampleState
--
--   Let $X$ be a type, $c : X \to \{0,1\}$ a concept, and $D : X \to \mathbb{R}$ an arbitrary real function. The definition is the vector $\psi_{c,D}$ in the complex Euclidean space with basis indexed by $X \times \{0,1\}$, with coordinates
--
--   $$\psi_{c,D}(x,b) = \begin{cases} \sqrt{D(x)} & \text{if } b = c(x),\\ 0 & \text{otherwise,}\end{cases}$$
--
--   that is, $\psi_{c,D} = \sum_x \sqrt{D(x)}\,|x, c(x)\rangle$.
--
--   The square root is the real square root, which the code sets to $0$ on negative arguments. No condition is placed on $D$, so the vector need not have unit norm. It has unit norm exactly when the clipped weights $\max(D(x),0)$ sum to $1$.
--
--   ### QAlgorithms.Learning.agnosticExampleState
--
--   Let $X$ be a type and $D : X \times \{0,1\} \to \mathbb{R}$ an arbitrary real function. The definition is the vector $\psi_D$ on the basis $X \times \{0,1\}$ with coordinates
--
--   $$\psi_D(x,b) = \sqrt{D(x,b)},$$
--
--   that is, $\psi_D = \sum_{(x,b)} \sqrt{D(x,b)}\,|x,b\rangle$. The real square root is taken, and it is $0$ for negative arguments. Unit norm is not imposed.
--
--   ### QAlgorithms.Learning.noisyExampleState
--
--   Let $X$ be a type, $\eta \in \mathbb{R}$ (a noise rate), $c : X \to \{0,1\}$ a concept, and $D : X \to \mathbb{R}$ an arbitrary real function. The definition is the vector $\psi^\eta_{c,D}$ on the basis $X \times \{0,1\}$ with coordinates
--
--   $$\psi^\eta_{c,D}(x,b) = \begin{cases} \sqrt{(1-\eta)\,D(x)} & \text{if } b = c(x),\\[2pt] \sqrt{\eta\, D(x)} & \text{if } b \neq c(x).\end{cases}$$
--
--   Each square root is the real square root, which is $0$ on negative arguments. No restriction is placed on $\eta$ (for instance $0 \le \eta \le 1$ or $\eta < 1/2$ is not required) or on $D$. With $\eta = 0$ this coincides with the example state $\sum_x \sqrt{D(x)}\,|x,c(x)\rangle$.
--
--   ### QAlgorithms.Learning.IsQPACLearner
--
--   **Setting.** Let $X$ be a finite type with decidable equality, $C$ a finite set of Boolean functions on $X$, $\varepsilon, \delta \in \mathbb{R}$ arbitrary, and $T \in \mathbb{N}$. Let $M = (M_h)_{h : X \to \{0,1\}}$ be a family of complex square matrices. The family is indexed by all hypotheses $h$, and each matrix acts on the space with basis $(X \times \{0,1\})^T$, i.e. $T$-tuples of labelled examples.
--
--   **Definition.** The predicate holds when both of the following are true:
--
--   1. $M$ is a POVM: every $M_h$ is positive semidefinite, and $\sum_h M_h = I$.
--
--   2. For every $c \in C$ and every $D : X \to \mathbb{R}$ that is a probability distribution ($D(x) \ge 0$ for all $x$ and $\sum_x D(x) = 1$),
--      $$\sum_{h:\ \mathrm{err}_D(c,h) \le \varepsilon} \operatorname{Re}\operatorname{tr}\!\big(M_h\, \rho\big) \;\ge\; 1-\delta.$$
--
--   **Meaning of the terms in (2).**
--
--   - The error is $\mathrm{err}_D(c,h) = \sum_{x:\,h(x)\neq c(x)} D(x)$.
--   - The state is $\rho = |\Psi\rangle\langle\Psi|$, the matrix with entries $\rho_{a,a'} = \Psi_a\overline{\Psi_{a'}}$.
--   - The vector $\Psi$ is the $T$-fold tensor power of the example state: $\Psi(z_1,\dots,z_T) = \prod_{i=1}^T \psi_{c,D}(z_i)$, with $\psi_{c,D}(x,b) = \sqrt{D(x)}$ if $b = c(x)$ and $0$ otherwise.
--
--   **Edge cases.**
--
--   - No constraints are placed on $\varepsilon$ or $\delta$. Every summand is nonnegative, so the condition in (2) is automatic when $\delta \ge 1$.
--   - When $T = 0$, the space is one-dimensional and $\rho = [1]$.
--   - If $C$ is empty, condition (2) is vacuous and only the POVM condition remains.
--
--   ### QAlgorithms.Learning.IsQAgnosticLearner
--
--   **Setting.** Let $X$ be a finite type with decidable equality, $C$ a finite set of Boolean functions on $X$, $\varepsilon, \delta \in \mathbb{R}$ arbitrary, and $T \in \mathbb{N}$. Let $M = (M_h)_{h \in C}$ be a family of complex square matrices indexed by the members of $C$ only. Each matrix acts on the space with basis $(X \times \{0,1\})^T$.
--
--   **Definition.** The predicate holds when both of the following are true:
--
--   1. $M$ is a POVM: each $M_h$ is positive semidefinite, and $\sum_{h\in C} M_h = I$.
--
--   2. For every $D : X \times \{0,1\} \to \mathbb{R}$ that is a probability distribution ($D \ge 0$ and $\sum_{(x,b)} D(x,b) = 1$),
--      $$\sum_{h \in C:\ \mathrm{err}_D(h) \le \mathrm{opt}_D(C) + \varepsilon} \operatorname{Re}\operatorname{tr}\!\big(M_h\,\rho\big) \;\ge\; 1-\delta.$$
--
--   **Meaning of the terms in (2).**
--
--   - The error is $\mathrm{err}_D(h) = \sum_{(x,b):\,h(x)\neq b} D(x,b)$.
--   - The benchmark is $\mathrm{opt}_D(C) = \inf_{c\in C}\mathrm{err}_D(c)$.
--   - The state is $\rho = |\Psi\rangle\langle\Psi|$ with entries $\rho_{a,a'} = \Psi_a\overline{\Psi_{a'}}$.
--   - The vector is $\Psi(z_1,\dots,z_T) = \prod_{i=1}^T \sqrt{D(z_i)}$.
--
--   **Edge cases.**
--
--   - No constraints are placed on $\varepsilon$ or $\delta$. The condition in (2) is automatic when $\delta \ge 1$.
--   - If $C$ is empty, the POVM condition requires $I = 0$. This is impossible unless the basis $(X\times\{0,1\})^T$ is empty, which happens exactly when $X$ is empty and $T \ge 1$.
--
--   ### QAlgorithms.Learning.IsNoisyQPACLearner
--
--   **Setting.** Let $X$ be a finite type with decidable equality, $\eta \in \mathbb{R}$ arbitrary, $C$ a finite set of Boolean functions on $X$, $\varepsilon, \delta \in \mathbb{R}$ arbitrary, and $T \in \mathbb{N}$. Let $M = (M_h)_{h : X\to\{0,1\}}$ be a family of complex square matrices indexed by all hypotheses. Each matrix acts on the space with basis $(X\times\{0,1\})^T$.
--
--   **Definition.** The predicate holds when both of the following are true:
--
--   1. $M$ is a POVM: each $M_h$ is positive semidefinite, and $\sum_h M_h = I$.
--
--   2. For every $c \in C$ and every probability distribution $D$ on $X$ ($D \ge 0$ and $\sum_x D(x) = 1$),
--      $$\sum_{h:\ \mathrm{err}_D(c,h) \le \varepsilon} \operatorname{Re}\operatorname{tr}\!\big(M_h\,\rho\big) \;\ge\; 1-\delta.$$
--
--   **Meaning of the terms in (2).**
--
--   - The error is $\mathrm{err}_D(c,h) = \sum_{x:\,h(x)\ne c(x)} D(x)$.
--   - The state is $\rho = |\Psi\rangle\langle\Psi|$.
--   - The vector is $\Psi(z_1,\dots,z_T) = \prod_{i=1}^T \psi^\eta_{c,D}(z_i)$.
--   - The one-example noisy state is $\psi^\eta_{c,D}(x,b) = \sqrt{(1-\eta)D(x)}$ if $b = c(x)$ and $\sqrt{\eta D(x)}$ otherwise, using real square roots, which are $0$ on negative arguments.
--
--   **Edge cases.**
--
--   - No range restriction is imposed on $\eta$. For $\eta < 0$ or $\eta > 1$, one of the two square roots is clipped to $0$, and $\Psi$ need not be a unit vector.
--   - No constraints are placed on $\varepsilon$ or $\delta$. The condition in (2) is automatic when $\delta \ge 1$.
--   - If $C$ is empty, condition (2) is vacuous.
--
--   ### QAlgorithms.Learning.IsPACLearner
--
--   This is a predicate on the following data:
--
--   - a finite instance set $X$ with decidable equality;
--   - a finite set $C$ of concepts $c : X \to \{0,1\}$ (Booleans, read as false/true);
--   - real parameters $\varepsilon, \delta$;
--   - a sample size $T \in \mathbb{N}$;
--   - a randomized learner $L$, which maps each labelled sample $s = ((x_1,b_1),\dots,(x_T,b_T)) \in (X \times \{0,1\})^T$ to a probability distribution $L(s)$ on the set of all hypotheses $h : X \to \{0,1\}$.
--
--   A *distribution* $D : X \to \mathbb{R}$ means $D(x) \ge 0$ for all $x$ and $\sum_x D(x) = 1$. The PAC error of $h$ with respect to target $c$ is
--
--   $$\mathrm{err}_D(c,h) = \sum_{x \in X,\ h(x) \ne c(x)} D(x).$$
--
--   The predicate holds iff, for every $c \in C$ and every distribution $D$ on $X$,
--
--   $$\sum_{(x_1,\dots,x_T) \in X^T} \Big(\prod_{i=1}^{T} D(x_i)\Big) \cdot \sum_{h : X \to \{0,1\},\ \mathrm{err}_D(c,h) \le \varepsilon} L\big((x_1,c(x_1)),\dots,(x_T,c(x_T))\big)(h) \;\ge\; 1 - \delta .$$
--
--   The left side is the probability that the learner outputs an $h$ with error at most $\varepsilon$. The sample consists of $T$ i.i.d. points from $D$, each labelled by $c$. The probability $L(s)(h)$ is an extended nonnegative real, converted to a real number.
--
--   Points to note:
--
--   - **Improper learners are allowed.** There is no requirement that the output $h$ lie in $C$.
--   - **$C = \emptyset$.** The condition holds vacuously.
--   - **$T = 0$.** The only sample is the empty one.
--   - **$\delta \ge 1$.** The left side is nonnegative, so the condition holds automatically.
--   - **$\varepsilon < 0$.** No $h$ qualifies, so the condition forces $\delta \ge 1$.
--
--   ### QAlgorithms.Learning.IsAgnosticLearner
--
--   The data are as for the PAC learner: a finite instance set $X$ with decidable equality, a finite concept class $C \subseteq \{0,1\}^X$, reals $\varepsilon, \delta$, a sample size $T \in \mathbb{N}$, and a randomized learner $L$. The learner maps samples $s \in (X \times \{0,1\})^T$ to probability distributions $L(s)$ on hypotheses $h : X \to \{0,1\}$.
--
--   For a distribution $D$ on $X \times \{0,1\}$ (nonnegative, summing to 1), define the agnostic error and the optimal error:
--
--   $$\mathrm{err}_D(h) = \sum_{(x,b)\,:\,h(x) \ne b} D(x,b), \qquad \mathrm{opt}_D(C) = \inf_{c \in C} \mathrm{err}_D(c).$$
--
--   The infimum is taken in $\mathbb{R}$, so it equals $0$ if $C = \emptyset$.
--
--   The predicate is the conjunction of two conditions:
--
--   1. **Properness.** For every sample $s$, every $h$ with $L(s)(h) > 0$ belongs to $C$.
--   2. **Success probability.** For every distribution $D$ on $X \times \{0,1\}$,
--
--   $$\sum_{s = (s_1,\dots,s_T) \in (X\times\{0,1\})^T} \Big(\prod_{i=1}^T D(s_i)\Big) \cdot \sum_{h\,:\,\mathrm{err}_D(h) \le \mathrm{opt}_D(C) + \varepsilon} L(s)(h) \;\ge\; 1-\delta.$$
--
--   In condition 2, the sample consists of $T$ i.i.d. labelled pairs drawn from $D$, and the probabilities are converted to reals.
--
--   If $C = \emptyset$, condition 1 cannot hold, because each $L(s)$ has nonempty support; the predicate is then false.
--
--   ### QAlgorithms.Learning.IsAvgAgnosticLearner
--
--   This is a predicate on four pieces of data:
--
--   - a finite instance space $X$ with decidable equality;
--   - a concept class $C$, a finite set of Boolean functions $c : X \to \{\text{false}, \text{true}\}$;
--   - a real accuracy parameter $\varepsilon$, with no sign constraint;
--   - a sample size $T \in \mathbb{N}$;
--   - a classical randomized learner $L$, which assigns to every labelled sample $s = (s_0, \dots, s_{T-1}) \in (X \times \{\text{false},\text{true}\})^T$ a probability distribution $L_s$ over *all* hypotheses $h : X \to \{\text{false},\text{true}\}$.
--
--   Nothing requires the hypotheses output by $L$ to lie in $C$.
--
--   The predicate holds when the following is true for every function $D : X \times \{\text{false},\text{true}\} \to \mathbb{R}$ that is a probability distribution, meaning $D(x,b) \ge 0$ for all $(x,b)$ and $\sum_{(x,b)} D(x,b) = 1$:
--   $$
--   \sum_{s \in (X\times\{\text{false},\text{true}\})^T} \Big(\prod_{i=0}^{T-1} D(s_i)\Big) \sum_{h : X \to \{\text{false},\text{true}\}} L_s(h)\,\mathrm{err}_D(h) \;-\; \mathrm{opt}_D(C) \;\le\; \varepsilon .
--   $$
--
--   The quantities in this inequality are as follows:
--
--   - $\mathrm{err}_D(h) = \sum_{(x,b)\,:\,h(x) \ne b} D(x,b)$ is the $D$-probability that $h$ mislabels a random labelled example.
--   - $\mathrm{opt}_D(C) = \inf_{c \in C} \mathrm{err}_D(c)$ is the infimum over the finite set $C$. When $C = \emptyset$, the infimum over the empty index set takes the real-number default value $0$.
--   - $L_s(h)$ is the probability mass that $L_s$ gives to $h$, converted from an extended non-negative real to a real number.
--
--   So the left-hand side is the expected error of the learner's output when the $T$ examples are drawn i.i.d. from $D$, minus the best error achievable in $C$. The condition bounds this excess by $\varepsilon$ in expectation only. It makes no high-probability (confidence) statement.
--
--   Edge cases:
--
--   - **$T = 0$.** There is exactly one (empty) sample, its weight is the empty product $1$, and the condition reads $\sum_h L_{\emptyset}(h)\,\mathrm{err}_D(h) - \mathrm{opt}_D(C) \le \varepsilon$ for every $D$.
--   - **$C = \emptyset$.** The condition becomes "expected error $\le \varepsilon$" for every $D$.
--   - **$\varepsilon < 0$.** The predicate can still be stated. It requires the learner to beat the best concept in $C$ by at least $|\varepsilon|$ for every $D$.
--
--   ### QAlgorithms.Learning.IsQExactLearner
--
--   The data are:
--
--   - finite types $\iota$ (query indices) and $W$ (workspace), each with decidable equality;
--   - a number of queries $T \in \mathbb{N}$, given implicitly;
--   - a $T$-query algorithm $A$;
--   - an output map $\mathrm{out}$ from basis labels $((i,b),w) \in (\iota \times \{0,1\}) \times W$ to strings in $\{0,1\}^\iota$;
--   - a finite concept class $C \subseteq \{0,1\}^\iota$.
--
--   The algorithm $A$ consists of a unit vector $\psi_0 \in \mathbb{C}^{(\iota\times\{0,1\})\times W}$ and unitaries $U_0,\dots,U_T$ on that space. On concept $c$, $A$ uses the XOR oracle
--
--   $$O_c\,|i,b\rangle = |i, b \oplus c_i\rangle$$
--
--   on the first two registers, tensored with the identity on $W$. Its final state is
--
--   $$\psi_c = U_T (O_c\otimes I) U_{T-1} \cdots U_1 (O_c\otimes I) U_0\, \psi_0 .$$
--
--   The predicate holds iff, for every $c \in C$,
--
--   $$\sum_{z\,:\,\mathrm{out}(z) = c} |\langle z|\psi_c\rangle|^2 \;\ge\; \tfrac23 .$$
--
--   That is, a computational-basis measurement of the final state, post-processed by $\mathrm{out}$, yields exactly $c$ with probability at least $2/3$. This is a bounded-error, not zero-error, requirement. The condition is vacuous when $C = \emptyset$.
--
--   ### QAlgorithms.Learning.quantumExactComplexity
--
--   For a finite type $\iota$ with decidable equality and a finite concept class $C \subseteq \{0,1\}^\iota$, this is the natural number
--
--   $$Q(C) = \min\{\,T \in \mathbb{N} : \exists\, w \in \mathbb{N},\ \exists\, A,\ \exists\, \mathrm{out},\ A \text{ quantum-exactly learns } C\,\}.$$
--
--   Here:
--
--   - $A$ is a $T$-query algorithm with query register $\iota\times\{0,1\}$ and workspace $\{0,\dots,w-1\}$;
--   - $\mathrm{out}$ is a map $(\iota\times\{0,1\})\times\{0,\dots,w-1\} \to \{0,1\}^\iota$;
--   - "quantum-exactly learns $C$" means the condition `IsQExactLearner` above: for each $c \in C$, the XOR-oracle run of $A$ followed by measurement and $\mathrm{out}$ returns $c$ with probability at least $2/3$.
--
--   Further points:
--
--   - The workspace dimension $w$ is an arbitrary natural number, not necessarily a power of 2.
--   - When $w = 0$, the state space is empty and no unit start vector exists, so effectively $w \ge 1$.
--   - By convention, the minimum of an empty set of naturals is $0$.
--   - If $C = \emptyset$, every $T$ qualifies and the value is $0$.
--
--   ### QAlgorithms.Learning.classicalExactComplexity
--
--   For a finite type $\iota$ with decidable equality and a finite concept class $C \subseteq \{0,1\}^\iota$, this is
--
--   $$R(C) = \min\{\,T \in \mathbb{N} : \exists\, R \text{ satisfying conditions (i) and (ii)}\,\}.$$
--
--   Here $R$ is a randomized decision tree: a probability distribution over deterministic decision trees. Each tree queries coordinates $i \in \iota$, branches on the Boolean answer, and outputs a string in $\{0,1\}^\iota$ at a leaf. The two conditions are:
--
--   - **(i) Query bound.** Every tree in the support of $R$ makes at most $T$ queries on every input $x \in \{0,1\}^\iota$. Repeated queries of the same index count separately.
--   - **(ii) Success probability.** For every $c \in C$, the probability over $R$ that the tree, run on input $c$, outputs exactly $c$ is at least $2/3$.
--
--   By convention, the minimum of an empty set of naturals is $0$. If $C = \emptyset$, $T = 0$ qualifies and the value is $0$.
--
--   ### QAlgorithms.Learning.quantumExactNM
--
--   For $n, M \in \mathbb{N}$, this is
--
--   $$Q(n,M) = \max\{\, Q(C) : C \subseteq \{0,1\}^{\{0,1\}^n},\ |C| = M \,\}.$$
--
--   Each concept is a Boolean function $c : \{0,1\}^n \to \{0,1\}$, viewed as a string of length $N = 2^n$ indexed by $n$-bit strings. $Q(C)$ is the quantum exact-learning complexity defined above.
--
--   The maximum is taken in $\mathbb{N}$ with value $0$ over the empty family. This happens when $M > 2^{2^n}$, since then no set of exactly $M$ such functions exists.
--
--   ### QAlgorithms.Learning.classicalExactNM
--
--   For $n, M \in \mathbb{N}$, this is
--
--   $$R(n,M) = \max\{\, R(C) : C \subseteq \{0,1\}^{\{0,1\}^n},\ |C| = M \,\}.$$
--
--   Here $R(C)$ is the classical randomized exact-learning complexity defined above. The concepts are Boolean functions on $n$-bit strings. The maximum is $0$ when no subset of size exactly $M$ exists, i.e. when $M > 2^{2^n}$.
--
--   ### QAlgorithms.Learning.gammaFrac
--
--   The data are an arbitrary index type $\iota$, a finite set $C'$ of strings $c : \iota \to \{0,1\}$, an index $i \in \iota$, and a bit $b$. The value is the real number
--
--   $$\gamma(C', i, b) = \frac{|\{c \in C' : c_i = b\}|}{|C'|}.$$
--
--   This is the fraction of strings in $C'$ whose $i$-th bit equals $b$. Division by zero yields $0$, so $\gamma(\emptyset, i, b) = 0$.
--
--   ### QAlgorithms.Learning.gammaPrime
--
--   For an arbitrary index type $\iota$ (not assumed finite) and a finite set $C'$ of strings $\iota \to \{0,1\}$, this is the real number
--
--   $$\gamma'(C') = \sup_{i \in \iota}\ \min\big(\gamma(C',i,0),\ \gamma(C',i,1)\big).$$
--
--   Here $\gamma(C',i,b)$ is the fraction of $c \in C'$ with $c_i = b$, taken to be $0$ when $C' = \emptyset$.
--
--   So $\gamma'(C')$ is the largest, over coordinates $i$, of the smaller of the two fractions of $C'$ with bit $i$ equal to $0$ and equal to $1$. All values lie in $[0,1]$, so the supremum is a genuine real supremum. When $\iota$ is empty, the supremum in $\mathbb{R}$ is by convention $0$.
--
--   ### QAlgorithms.Learning.gammaParam
--
--   For an arbitrary index type $\iota$ and a finite set $C$ of strings $\iota \to \{0,1\}$, this is the real number
--
--   $$\gamma(C) = \inf\{\, \gamma'(C') : C' \subseteq C,\ |C'| \ge 2 \,\}.$$
--
--   Here $\gamma'(C') = \sup_{i}\min(\text{fraction of } C' \text{ with } c_i = 0,\ \text{fraction with } c_i = 1)$, as defined above.
--
--   The infimum ranges over all subsets of $C$ with at least two elements. If $|C| < 2$, there is no such subset, and by the real-infimum convention the value is $0$.
--
--   ### QAlgorithms.Learning.EffectSet
--
--   For $n \in \mathbb{N}$, this is the set of effects (two-outcome measurement operators) on $n$ qubits:
--
--   $$\mathcal{E}_n = \{\, E \in \mathbb{C}^{2^n \times 2^n} : E \text{ satisfies (a) and (b)} \,\}.$$
--
--   Rows and columns of $E$ are indexed by $n$-bit strings. The two conditions are:
--
--   - **(a)** $E$ is positive semidefinite, which includes being Hermitian.
--   - **(b)** $I - E$ is positive semidefinite.
--
--   Equivalently, $0 \preceq E \preceq I$. Elements of $\mathcal{E}_n$ are such matrices together with the proof of the two conditions.
--
--   ### QAlgorithms.Learning.effectSampleLaw
--
--   This defines a measure $\Lambda_{D,\rho}$ on the product $\mathrm{Eff}_n \times \{\mathsf{true},\mathsf{false}\}$. Its inputs are:
--
--   - a natural number $n$;
--   - a measure $D$ on $\mathrm{Eff}_n$ (Borel $\sigma$-algebra), where $\mathrm{Eff}_n$ is the set of complex $2^n\times 2^n$ matrices $E$, indexed by $\{0,1\}^n$, with $E \succeq 0$ and $I - E \succeq 0$;
--   - an arbitrary complex $2^n\times 2^n$ matrix $\rho$.
--
--   No hypothesis is placed on $\rho$: it need not be positive semidefinite, Hermitian, or of trace $1$. Likewise, $D$ need not be a probability measure or even finite.
--
--   For an effect $E$, write
--   $$p_\rho(E) = \operatorname{Re}\operatorname{tr}(E\rho).$$
--
--   The measure is the sum of two pieces:
--
--   - the measure on $\mathrm{Eff}_n$ with density $\max\{p_\rho(E),0\}$ with respect to $D$, pushed forward along $E \mapsto (E,\mathsf{true})$;
--   - the measure on $\mathrm{Eff}_n$ with density $\max\{1-p_\rho(E),0\}$ with respect to $D$, pushed forward along $E \mapsto (E,\mathsf{false})$.
--
--   Concretely, for a measurable set $A \subseteq \mathrm{Eff}_n$:
--   $$\Lambda_{D,\rho}(A\times\{\mathsf{true}\}) = \int_A \max\{\operatorname{Re}\operatorname{tr}(E\rho),\,0\}\,dD(E),$$
--   $$\Lambda_{D,\rho}(A\times\{\mathsf{false}\}) = \int_A \max\{1-\operatorname{Re}\operatorname{tr}(E\rho),\,0\}\,dD(E).$$
--
--   Two details of the definition matter:
--
--   - **Truncation.** Each density is cut off at $0$. Any negative value of $p_\rho(E)$ or of $1-p_\rho(E)$ is replaced by $0$. This can happen when $\rho$ is not a density matrix.
--   - **Total mass.** The total mass equals $D(\mathrm{Eff}_n)$ only when $0 \le p_\rho(E) \le 1$ for $D$-almost every $E$. That holds, for instance, when $\rho$ is a density matrix. Otherwise the total mass can differ from $D(\mathrm{Eff}_n)$, and it is $1$ only if $D$ is additionally a probability measure.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Learning.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_BooleanFourier
/-!
# Learning models: exact, PAC and agnostic learning from classical or quantum data
(shared definition layer)

S. Arunachalam, R. de Wolf, *A survey of quantum learning theory* (2017), cited "survey p.N", and
S. Arunachalam, *Quantum Algorithms and Learning Theory* (PhD thesis, 2018), Chapters 6–7, cited
"Arunachalam p.N" (PDF pages).

Conventions:
* A concept is a Boolean function `c : X → Bool` on a finite domain `X` (`X = Qubits n` for the
  source's `{0,1}^n`; `true` is the label `1`), and a concept class is a `Finset (X → Bool)`.
* A distribution on a finite set is a real weight function (`IsDistribution`), so that the
  amplitudes `√D(x)` of quantum examples and the error probabilities are plain sums.
* A learner "using T examples" is modelled as one using exactly `T` (a learner using fewer can
  ignore the rest). A quantum learner is a POVM on `T` copies of the example state, one outcome per
  hypothesis; ancillas and internal randomness are absorbed into the POVM. A classical learner is
  a randomized map (a `PMF` over hypotheses) from the `T` labelled samples. The learner is fixed
  before the target concept and the distribution.
* Exact learners use membership queries: quantum ones the frozen `QueryAlg` with the XOR oracle
  `QMQ(c) = xorOracle c : |x, b⟩ ↦ |x, b ⊕ c(x)⟩`, classical ones randomized decision trees
  (`MQ(c)`; internal randomness is the distribution over trees).
-/

namespace QAlgorithms.Learning

open scoped ComplexConjugate ComplexOrder

open MeasureTheory

/-- Survey p.7 (§3.2, `D : {0,1}^n → [0,1]`), p.8 (§3.3, `D : {0,1}^{n+1} → [0,1]`), Arunachalam
p.127 (§6.3.2): a probability distribution on a finite set `X`, as a nonnegative real weight
function summing to `1`. -/
def IsDistribution {X : Type*} [Fintype X] (D : X → ℝ) : Prop :=
  (∀ x, 0 ≤ D x) ∧ ∑ x, D x = 1

/-- Arunachalam p.182 (§7.6.2, "drawn uniformly at random"): the uniform distribution
`D(x) = 1/|X|` on a finite set `X`. -/
noncomputable def uniformDist (X : Type*) [Fintype X] : X → ℝ :=
  fun _ => ((Fintype.card X : ℝ))⁻¹

/-- Survey p.7 (§3.2), Arunachalam p.127 (§6.3.2), p.169 (§7.6.1): the error of the hypothesis
`h` with respect to the target concept `c` under `D`, `err_D(h, c) = Pr_{x∼D}[h(x) ≠ c(x)]`. -/
noncomputable def pacError {X : Type*} [Fintype X] (D : X → ℝ) (c h : X → Bool) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => h x ≠ c x), D x

/-- Survey p.8 (§3.3), Arunachalam p.129 (§6.3.3): the error of `h` under a distribution `D` on
labelled pairs, `err_D(h) = Pr_{(x,b)∼D}[h(x) ≠ b]`. -/
noncomputable def agnosticError {X : Type*} [Fintype X] (D : X × Bool → ℝ) (h : X → Bool) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p : X × Bool => h p.1 ≠ p.2), D p

/-- Survey p.8 (§3.3), Arunachalam p.129 (§6.3.3): `opt_D(C) = min_{c ∈ C} err_D(c)`, a minimum
over a finite set (so attained). Junk: `0` for an empty class; every statement using it has `C`
nonempty. -/
noncomputable def optError {X : Type*} [Fintype X] (D : X × Bool → ℝ) (C : Finset (X → Bool)) :
    ℝ :=
  ⨅ c : {c // c ∈ C}, agnosticError D c.1

/-- Survey p.12 (Def. 4.10), Arunachalam p.137 (Def. 6.5.1): the VC dimension of `C`, the size of
a largest `S ⊆ X` shattered by `C` (every labelling of `S` is realized by some `c ∈ C`). Computed
as Mathlib's `Finset.vcDim` of the family of supports `{x | c x = true}`: `S` is shattered by the
supports (`∀ t ⊆ S, ∃ c, S ∩ supp c = t`) iff every labelling of `S` is realized. Edge: an empty
class gets `0` (the source's value is undefined; statements fix the VC dimension `≥ 1`). -/
def vcDimClass {X : Type*} [Fintype X] [DecidableEq X] (C : Finset (X → Bool)) : ℕ :=
  (C.image fun c => Finset.univ.filter fun x => c x = true).vcDim

/-- Arunachalam p.163 (footnote 5): `C` is non-trivial, i.e. neither a single concept nor exactly
two complementary concepts `{c, 1 − c}` (and not empty). -/
def IsNontrivialClass {X : Type*} [DecidableEq X] [Fintype X] (C : Finset (X → Bool)) : Prop :=
  2 ≤ C.card ∧ ¬ ∃ c : X → Bool, C = {c, fun x => !c x}

/-- Survey p.7 (§3.2), Arunachalam p.127 (§6.3.2): the quantum example
`QPEX(c, D) = ∑_x √D(x) |x, c(x)⟩`, with real amplitudes (survey p.7, footnote 6). It is a unit
vector exactly when `∑ D = 1`. -/
noncomputable def exampleState {X : Type*} (c : X → Bool) (D : X → ℝ) :
    EuclideanSpace ℂ (X × Bool) :=
  WithLp.toLp 2 fun p => if p.2 = c p.1 then (Real.sqrt (D p.1) : ℂ) else 0

/-- Survey p.8 (§3.3), Arunachalam p.129 (§6.3.3): the quantum agnostic example
`QAEX(D) = ∑_{(x,b)} √D(x,b) |x, b⟩`. -/
noncomputable def agnosticExampleState {X : Type*} (D : X × Bool → ℝ) :
    EuclideanSpace ℂ (X × Bool) :=
  WithLp.toLp 2 fun p => (Real.sqrt (D p) : ℂ)

/-- Arunachalam p.158 (§7.1) and p.169 (§7.6.1): the `η`-noisy quantum example
`∑_x √((1−η)D(x)) |x, c(x)⟩ + √(ηD(x)) |x, 1 − c(x)⟩`. At `η = 0` it is `exampleState c D`. -/
noncomputable def noisyExampleState {X : Type*} (η : ℝ) (c : X → Bool) (D : X → ℝ) :
    EuclideanSpace ℂ (X × Bool) :=
  WithLp.toLp 2 fun p =>
    if p.2 = c p.1 then (Real.sqrt ((1 - η) * D p.1) : ℂ) else (Real.sqrt (η * D p.1) : ℂ)

/-- Survey p.7 (§3.2), Arunachalam p.128 (§6.3.2): `M` is an `(ε, δ)`-quantum PAC learner for
`C` using `T` quantum examples: a POVM on `T` copies of the quantum example, with one outcome per
hypothesis `h : X → Bool` (not required to lie in `C`), such that for every `c ∈ C` and every
distribution `D`, measuring `|ψ_{c,D}⟩^{⊗T}` yields an `h` with `err_D(h, c) ≤ ε` with probability
at least `1 − δ`. -/
def IsQPACLearner {X : Type*} [Fintype X] [DecidableEq X] (C : Finset (X → Bool)) (ε δ : ℝ)
    (T : ℕ) (M : (X → Bool) → Matrix (Fin T → X × Bool) (Fin T → X × Bool) ℂ) : Prop :=
  IsPOVM M ∧ ∀ c ∈ C, ∀ D : X → ℝ, IsDistribution D →
    povmEventProb M (pureDensity (tensorPow T (exampleState c D)))
      (fun h => pacError D c h ≤ ε) ≥ 1 - δ

/-- Survey p.8 (§3.3), Arunachalam p.129 (§6.3.3): `M` is an `(ε, δ)`-quantum agnostic learner
for `C` using `T` quantum examples: a POVM on `T` copies of `QAEX(D)` whose outcomes are the
concepts of `C` (the learner outputs `h ∈ C`), such that for every distribution `D` on
`X × {0,1}` the outcome `h` satisfies `err_D(h) ≤ opt_D(C) + ε` with probability at least
`1 − δ`. -/
def IsQAgnosticLearner {X : Type*} [Fintype X] [DecidableEq X] (C : Finset (X → Bool)) (ε δ : ℝ)
    (T : ℕ) (M : {c // c ∈ C} → Matrix (Fin T → X × Bool) (Fin T → X × Bool) ℂ) : Prop :=
  IsPOVM M ∧ ∀ D : X × Bool → ℝ, IsDistribution D →
    povmEventProb M (pureDensity (tensorPow T (agnosticExampleState D)))
      (fun h => agnosticError D h.1 ≤ optError D C + ε) ≥ 1 - δ

/-- Arunachalam p.169 (§7.6.1): `M` is an `(ε, δ)`-quantum PAC learner for `C` under random
classification noise of rate `η`, using `T` copies of the `η`-noisy quantum example: as
`IsQPACLearner`, with the noisy example state; success is still measured by the noiseless
`err_D(c, h) ≤ ε`. -/
def IsNoisyQPACLearner {X : Type*} [Fintype X] [DecidableEq X] (η : ℝ) (C : Finset (X → Bool))
    (ε δ : ℝ) (T : ℕ) (M : (X → Bool) → Matrix (Fin T → X × Bool) (Fin T → X × Bool) ℂ) : Prop :=
  IsPOVM M ∧ ∀ c ∈ C, ∀ D : X → ℝ, IsDistribution D →
    povmEventProb M (pureDensity (tensorPow T (noisyExampleState η c D)))
      (fun h => pacError D c h ≤ ε) ≥ 1 - δ

/-- Survey p.6 (§3.2), Arunachalam p.127 (§6.3.2), p.152 (§7.1.1): `L` is a classical
`(ε, δ)`-PAC learner for `C` using `T` examples: a randomized map from `T` labelled examples to a
hypothesis `h : X → Bool` (not required to lie in `C`) such that, for every `c ∈ C` and every
distribution `D`, when the examples `(x_i, c(x_i))` have `x_1, …, x_T` i.i.d. from `D`, the
output satisfies `err_D(h, c) ≤ ε` with probability at least `1 − δ` (over the samples and the
learner's randomness). -/
def IsPACLearner {X : Type*} [Fintype X] [DecidableEq X] (C : Finset (X → Bool)) (ε δ : ℝ)
    (T : ℕ) (L : (Fin T → X × Bool) → PMF (X → Bool)) : Prop :=
  ∀ c ∈ C, ∀ D : X → ℝ, IsDistribution D →
    ∑ xs : Fin T → X, (∏ i, D (xs i)) *
      ∑ h : X → Bool, (if pacError D c h ≤ ε then (L fun i => (xs i, c (xs i))) h else 0).toReal
      ≥ 1 - δ

/-- Survey p.8 (§3.3), Arunachalam p.129 (§6.3.3), p.153 (§7.1.2): `L` is a classical
`(ε, δ)`-agnostic learner for `C` using `T` examples: a randomized map from `T` labelled samples
to a hypothesis in `C` such that, for every distribution `D` on `X × {0,1}` and `T` i.i.d.
samples from `D`, the output satisfies `err_D(h) ≤ opt_D(C) + ε` with probability at least
`1 − δ`. -/
def IsAgnosticLearner {X : Type*} [Fintype X] [DecidableEq X] (C : Finset (X → Bool)) (ε δ : ℝ)
    (T : ℕ) (L : (Fin T → X × Bool) → PMF (X → Bool)) : Prop :=
  (∀ s, ∀ h ∈ (L s).support, h ∈ C) ∧
    ∀ D : X × Bool → ℝ, IsDistribution D →
      ∑ s : Fin T → X × Bool, (∏ i, D (s i)) *
        ∑ h : X → Bool, (if agnosticError D h ≤ optError D C + ε then L s h else 0).toReal
        ≥ 1 - δ

/-- Arunachalam p.166 (§7.4.3): `L` is a classical `ε`-average agnostic learner for `C` using `T`
samples: it outputs a hypothesis `h_{XY} : X → {0,1}` (the definition does not require
`h_{XY} ∈ C`, unlike the `(ε, δ)`-agnostic learner of p.117) and, for every distribution `D` on
`X × {0,1}`, `E_{(X,Y)∼D^T}[err_D(h_{XY})] − opt_D(C) ≤ ε` (the expectation also over the
learner's randomness). -/
def IsAvgAgnosticLearner {X : Type*} [Fintype X] [DecidableEq X] (C : Finset (X → Bool)) (ε : ℝ)
    (T : ℕ) (L : (Fin T → X × Bool) → PMF (X → Bool)) : Prop :=
  ∀ D : X × Bool → ℝ, IsDistribution D →
    (∑ s : Fin T → X × Bool, (∏ i, D (s i)) *
      ∑ h : X → Bool, (L s h).toReal * agnosticError D h) - optError D C ≤ ε

/-- Survey p.6 (§3.1), p.4 (§2.2), Arunachalam p.126 (§6.3.1): the `T`-query quantum algorithm
`A` (frozen `QueryAlg`: input-independent unitaries, fixed workspace `W`) with output map `out`
is a quantum exact learner for `C`: for every target `c ∈ C`, run with the membership oracle
`QMQ(c) : |x, b⟩ ↦ |x, b ⊕ c(x)⟩`, it outputs `h = c` with probability at least `2/3`
(footnote 4). -/
def IsQExactLearner {ι W : Type*} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (out : (ι × Bool) × W → (ι → Bool)) (C : Finset (ι → Bool)) :
    Prop :=
  ∀ c ∈ C, A.outputProb (xorOracle c) out c ≥ 2 / 3

/-- Survey p.6 (§3.1): the quantum query complexity `Q(C)` of exactly learning `C`, the least
`T` such that some `T`-query quantum exact learner for `C` exists (any finite workspace
`Fin w`). The set is nonempty (`|ι|` queries copying the truth table suffice), so the `sInf` is
the source's minimum. -/
noncomputable def quantumExactComplexity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset (ι → Bool)) : ℕ :=
  sInf {T : ℕ | ∃ (w : ℕ) (A : QueryAlg ι Bool (Fin w) T) (out : (ι × Bool) × Fin w → (ι → Bool)),
    IsQExactLearner A out C}

/-- Survey p.6 (§3.1): the classical query complexity `D(C)` of exactly learning `C` with
membership queries, the least `T` such that a randomized decision tree making at most `T` queries
outputs `c` with probability at least `2/3` for every target `c ∈ C`. The query bound is imposed
on every input, which changes nothing (cut each tree at depth `T`: the paths of the targets are
unaffected). The set is nonempty (query every index), so the `sInf` is the source's minimum. -/
noncomputable def classicalExactComplexity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset (ι → Bool)) : ℕ :=
  sInf {T : ℕ | ∃ R : RandDecisionTree ι Bool (ι → Bool), RandMakesAtMost R T ∧
    ∀ c ∈ C, successProb R c c ≥ 2 / 3}

/-- Survey p.6 (§3.1): the `(N, M)`-quantum query complexity of exact learning, `N = 2^n`, the
maximum of `Q(C)` over all classes `C ⊆ {0,1}^N` of size `M`. Junk `0` when `M > 2^N` (no such
class); statements carry `M ≤ 2^N`. -/
noncomputable def quantumExactNM (n M : ℕ) : ℕ :=
  ((Finset.univ : Finset (Qubits n → Bool)).powersetCard M).sup quantumExactComplexity

/-- Survey p.6 (§3.1): the classical `(N, M)`-query complexity of exact learning, `N = 2^n`, the
maximum of `D(C)` over all classes of size `M` (junk `0` when `M > 2^N`). -/
noncomputable def classicalExactNM (n M : ℕ) : ℕ :=
  ((Finset.univ : Finset (Qubits n → Bool)).powersetCard M).sup classicalExactComplexity

/-- Survey p.8 (Def. 4.1): `γ'(C', i, b) = |{c ∈ C' : c_i = b}| / |C'|`, the fraction of the
concepts in `C'` with `c_i = b`. Junk `0` at `C' = ∅`, never used (`γ` ranges over
`|C'| ≥ 2`). -/
noncomputable def gammaFrac {ι : Type*} (C' : Finset (ι → Bool)) (i : ι) (b : Bool) : ℝ :=
  ((C'.filter fun c => c i = b).card : ℝ) / (C'.card : ℝ)

/-- Survey p.8 (Def. 4.1): `γ'(C') = max_{i ∈ [N]} min{γ'(C', i, 0), γ'(C', i, 1)}`, a maximum
over the finite nonempty index set (`Qubits n` always has a point). -/
noncomputable def gammaPrime {ι : Type*} (C' : Finset (ι → Bool)) : ℝ :=
  ⨆ i : ι, min (gammaFrac C' i false) (gammaFrac C' i true)

/-- Survey p.8 (Def. 4.1): `γ(C) = min_{C' ⊆ C, |C'| ≥ 2} γ'(C')`, defined by the source for
`|C| > 1`; the minimum over a finite nonempty family. Lean's value for `|C| ≤ 1` is the junk `0`
(empty index), excluded by `2 ≤ C.card` in every statement. -/
noncomputable def gammaParam {ι : Type*} (C : Finset (ι → Bool)) : ℝ :=
  ⨅ C' : {C' : Finset (ι → Bool) // C' ⊆ C ∧ 2 ≤ C'.card}, gammaPrime C'.1

/-- Survey p.15 (§4.4): the set of two-outcome measurements on `n` qubits, given by the operator
`E` of the first outcome with `0 ≤ E ≤ I` (frozen `IsEffect`), with the subspace topology of the
matrices. -/
abbrev EffectSet (n : ℕ) := {E : Matrix (Qubits n) (Qubits n) ℂ // IsEffect E}

/-- Survey p.15 (§4.4): distributions `D` on the set of two-outcome measurements are Borel
probability measures for the subspace topology. -/
noncomputable instance (n : ℕ) : MeasurableSpace (EffectSet n) := borel (EffectSet n)

/-- The σ-algebra on `EffectSet n` is the Borel σ-algebra (survey p.15). -/
instance (n : ℕ) : BorelSpace (EffectSet n) := ⟨rfl⟩

/-- Survey p.15 (§4.4) and p.16 (Thm 4.16): the law of one measurement result `(E, b)`: `E` is
drawn from `D`, and given `E` the bit `b` is `1` with probability `Tr(Eρ)`. Written as the sum of
the two parts `b = 1` (density `Tr(Eρ)`) and `b = 0` (density `1 − Tr(Eρ)`), so that no kernel
measurability is involved. `T` i.i.d. results are `Measure.pi fun _ : Fin T => effectSampleLaw D ρ`.
-/
noncomputable def effectSampleLaw {n : ℕ} (D : Measure (EffectSet n))
    (ρ : Matrix (Qubits n) (Qubits n) ℂ) : Measure (EffectSet n × Bool) :=
  (D.withDensity fun E => ENNReal.ofReal (effectProb E.1 ρ)).map (fun E => (E, true)) +
    (D.withDensity fun E => ENNReal.ofReal (1 - effectProb E.1 ρ)).map (fun E => (E, false))

/-! ### Sanity tests -/

example {X : Type*} [Fintype X] (D : X → ℝ) (c : X → Bool) : pacError D c c = 0 := by
  simp [pacError]

example {X : Type*} (c : X → Bool) (D : X → ℝ) : noisyExampleState 0 c D = exampleState c D := by
  ext p
  simp [noisyExampleState, exampleState]

theorem exampleState_norm {X : Type*} [Fintype X] {D : X → ℝ} (hD : IsDistribution D)
    (c : X → Bool) : ‖exampleState c D‖ = 1 := by
  have hsq : ‖exampleState c D‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    rw [← hD.2]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_bool]
    cases h : c x <;>
      simp [exampleState, h, Complex.norm_real, Real.sq_sqrt (hD.1 x)]
  have h0 : 0 ≤ ‖exampleState c D‖ := norm_nonneg _
  nlinarith [hsq, h0]

example {X : Type*} [DecidableEq X] [Fintype X] (c : X → Bool) : ¬ IsNontrivialClass {c} := by
  simp [IsNontrivialClass]

example {ι : Type*} (i : ι) (b : Bool) : gammaFrac (∅ : Finset (ι → Bool)) i b = 0 := by
  simp [gammaFrac]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → Bool) :
    classicalExactComplexity {c} = 0 := by
  refine Nat.sInf_eq_zero.2 (Or.inl ⟨PMF.pure (DecisionTree.leaf c), ?_, ?_⟩)
  · intro t ht x
    rw [PMF.support_pure, Set.mem_singleton_iff] at ht
    subst ht
    rfl
  · intro c' hc'
    rw [Finset.mem_singleton] at hc'
    subst hc'
    simp [successProb, PMF.pure_map, DecisionTree.eval]
    norm_num

example {n : ℕ} (ρ : Matrix (Qubits n) (Qubits n) ℂ) : effectSampleLaw 0 ρ = 0 := by
  simp [effectSampleLaw]

end QAlgorithms.Learning


